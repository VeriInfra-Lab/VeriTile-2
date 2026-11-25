"""Check the pinned T04 source without importing torch, Triton or the tutorial.

The kernel theorem assumes the host gathers the indicated whole rows byte-exactly.
Source and shape checks here do not execute torch.concat or prove that premise.
"""
import ast
import hashlib
import operator
from pathlib import Path
import unittest


SOURCE = Path(__file__).parent / 'fixtures' / '04-deepseek-infer-all2all.py.txt'
BLOB = '25ba82233603691cebd52f96e53d6cabda8d375a'


class Polynomial(dict):
    """Sparse integer coefficients on sorted tuples of independent variables."""

    @classmethod
    def var(cls, name):
        return cls({(name,): 1})

    @classmethod
    def constant(cls, n):
        return cls({(): n}) if n else cls()

    @classmethod
    def coerce(cls, x):
        return x if isinstance(x, cls) else cls.constant(x)

    def __add__(self, other):
        result = Polynomial(self)
        for term, coefficient in self.coerce(other).items():
            result[term] = result.get(term, 0) + coefficient
            if not result[term]:
                del result[term]
        return result

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-1) * self.coerce(other)

    def __mul__(self, other):
        result = Polynomial()
        for left, a in self.items():
            for right, b in self.coerce(other).items():
                term = tuple(sorted(left + right))
                result[term] = result.get(term, 0) + a * b
        return Polynomial((term, c) for term, c in result.items() if c)

    __rmul__ = __mul__

    def __floordiv__(self, divisor):
        if not isinstance(divisor, int) or divisor <= 0 or any(c % divisor for c in self.values()):
            raise ValueError("floor division is not exact for every symbolic valuation")
        return Polynomial((term, c // divisor) for term, c in self.items())


def value(expr, env):
    """Interpret only the integer operations used in the pinned offsets/count."""
    if isinstance(expr, ast.Constant):
        return expr.value
    if isinstance(expr, (ast.Name, ast.Attribute)):
        return env[ast.unparse(expr)]
    if isinstance(expr, ast.IfExp):
        return value(expr.body if value(expr.test, env) else expr.orelse, env)
    if isinstance(expr, ast.BoolOp) and isinstance(expr.op, ast.And):
        return all(value(term, env) for term in expr.values)
    if isinstance(expr, ast.Compare) and len(expr.ops) == 1 and isinstance(expr.ops[0], ast.Eq):
        return value(expr.left, env) == value(expr.comparators[0], env)
    if isinstance(expr, ast.BinOp):
        op = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul, ast.FloorDiv: operator.floordiv}
        return op[type(expr.op)](value(expr.left, env), value(expr.right, env))
    raise ValueError(ast.dump(expr))


class T04PointerContract(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = SOURCE.read_bytes()
        cls.tree = ast.parse(cls.raw)

    def node(self, line, kind, root=None):
        nodes = [n for n in ast.walk(self.tree if root is None else root)
                 if isinstance(n, kind) and n.lineno == line]
        self.assertEqual(len(nodes), 1, (line, kind))
        return nodes[0]

    def stmt(self, line, expected):
        """Exact statement shape, ignoring whitespace, comments and positions."""
        actual = self.node(line, ast.stmt)
        self.assertEqual(ast.dump(actual), ast.dump(ast.parse(expected).body[0]))
        return actual

    def test_source_pin(self):
        header = f'blob {len(self.raw)}\0'.encode()
        self.assertEqual(hashlib.sha1(header + self.raw).hexdigest(), BLOB)

    def test_host_gather_and_row_units(self):
        self.stmt(463, 'GROUP_SIZE = 128')
        self.assertEqual(ast.unparse(self.node(464, ast.Assert).test), 'args.N % GROUP_SIZE == 0')
        kwargs = self.node(538, ast.Dict)
        launch = {k.value: ast.unparse(v) for k, v in zip(kwargs.keys, kwargs.values)}
        self.assertEqual((launch['HIDDEN'], launch['FP8_GSIZE']), ('args.N', 'GROUP_SIZE'))
        self.stmt(574, 'data_buf_st, data_buf_size = act_pos * (WORLD_SIZE * MAX_NUM_TOKENS), WORLD_SIZE * MAX_NUM_TOKENS')
        self.stmt(578, 'dis_tokens_buf = recv_buf[data_buf_st:data_buf_st + data_buf_size, :]')
        self.stmt(588, 'off, token_vec, scale_vec = 0, [], []')
        online = self.node(590, ast.If)
        self.assertEqual(ast.unparse(online.test), 'ONLINE_QUANT')
        gather = self.stmt(591, 'token_vec.append(dis_tokens_buf.reshape(-1, args.N // 2)[off * 2:off * 2 + ntk])')
        self.assertIs(online.body[0], gather)
        self.stmt(597, 'off += MAX_NUM_TOKENS')
        self.stmt(598, 'dispatched_tokens, s = torch.concat(token_vec), torch.concat(scale_vec) if ONLINE_QUANT else None')
        self.stmt(602, 'if ONLINE_QUANT: dispatched_tokens = dequant_fp8_bf16(dispatched_tokens, s)')

        selected = gather.value.args[0]
        width = selected.value.args[1]
        put = self.node(233, ast.Call)
        self.assertEqual(ast.unparse(put.args[2]),
                         'num_rows_cur_block * HIDDEN * (1 if ONLINE_QUANT_FP8 and MODE == 0 else 2)')
        # Derive the host count from the transmitted expert splits before
        # using the result as the device row count in the identities below.
        rows = self.dispatch_rows_from_split_packet()
        groups, off = map(Polynomial.var, ('g', 'off'))
        n = self.node(463, ast.Assign).value.value * groups
        symbolic = {'args.N': n, 'HIDDEN': n, 'off': off, 'ntk': rows,
                    'num_rows_cur_block': rows, 'ONLINE_QUANT_FP8': True, 'MODE': 0}
        row_bytes = value(width, symbolic) * 2
        first = value(selected.slice.lower, symbolic) * row_bytes
        end = value(selected.slice.upper, symbolic) * row_bytes
        self.assertEqual(row_bytes, n)
        self.assertEqual(first, 2 * off * n)
        self.assertEqual(end - first, rows * n)
        self.assertEqual(value(put.args[2], symbolic), end - first)

        # Concrete cases additionally check divmod and zero-length transfers.
        for n in (128 * groups for groups in (*range(1, 65), 127, 128)):
            for offset, rows in ((0, 0), (0, 1), (17, 3), (256, 16), (512, 255)):
                env = {'args.N': n, 'HIDDEN': n, 'off': offset, 'ntk': rows,
                       'num_rows_cur_block': rows, 'ONLINE_QUANT_FP8': True, 'MODE': 0}
                row_bytes = value(width, env) * 2
                first = value(selected.slice.lower, env) * row_bytes
                end = value(selected.slice.upper, env) * row_bytes
                self.assertEqual(row_bytes, n)
                self.assertEqual(divmod(first, n), (2 * offset, 0))
                self.assertEqual(end - first, rows * n)
                self.assertEqual(value(put.args[2], env), end - first)

    def dispatch_rows_from_split_packet(self):
        """Host ntk sums precisely the prefix differences stored for one sender."""
        self.stmt(143, 'EXPERTS_PER_RANK: tl.constexpr = NUM_TOT_EXPERTS // WORLD_SIZE')
        self.stmt(146, 'exp_st = pid * EXPERTS_PER_RANK')
        self.stmt(147, 'exp_ed = exp_st + EXPERTS_PER_RANK')
        self.stmt(148, 'm_st = tl.load(send_splits_cumsum + exp_st)')
        self.stmt(149, 'm_ed = tl.load(send_splits_cumsum + exp_ed)')
        device_rows = self.stmt(150, 'num_rows_cur_block = m_ed - m_st').value
        self.stmt(156, 'split_src_ptr = splits_src + (exp_st + pid)')
        self.stmt(157, 'split_dst_ptr = splits_dst + act_pos * (NUM_TOT_EXPERTS + WORLD_SIZE) + rank * (EXPERTS_PER_RANK + 1)')
        self.stmt(160, 'off0 = exp_st + tl.arange(0, EXPERTS_PER_RANK)')
        self.stmt(161, 'off1 = exp_st + tl.arange(0, EXPERTS_PER_RANK) + 1')
        self.stmt(162, 'cumsum_sts = tl.load(send_splits_cumsum + off0)')
        self.stmt(163, 'cumsum_eds = tl.load(send_splits_cumsum + off1)')
        store = self.stmt(164, 'tl.store(split_src_ptr + tl.arange(0, EXPERTS_PER_RANK), cumsum_eds - cumsum_sts)')
        delta = store.value.args[1]
        self.stmt(166, 'tl.store(split_src_ptr + EXPERTS_PER_RANK, m_st)')
        self.assertEqual(ast.unparse(self.node(240, ast.If).test), 'MODE == 0')
        self.stmt(242, 'libshmem_device.putmem_nbi_block(split_dst_ptr, split_src_ptr, (EXPERTS_PER_RANK + 1) * 4, pid)')
        self.assertEqual(ast.unparse(self.node(455, ast.Assert).test), 'args.G % WORLD_SIZE == 0')
        self.stmt(459, 'EXPERTS_PER_RANK = args.G // WORLD_SIZE')
        kwargs = self.node(538, ast.Dict)
        launch = {k.value: ast.unparse(v) for k, v in zip(kwargs.keys, kwargs.values)}
        self.assertEqual((launch['NUM_TOT_EXPERTS'], launch['WORLD_SIZE']), ('args.G', 'WORLD_SIZE'))
        dispatch = self.node(552, ast.Call)
        self.assertEqual([ast.unparse(a) for a in dispatch.args[5:9]],
                         ['split_send_buf', 'split_recv_buf', 'signal_buf', 'split_cumsum'])
        self.stmt(572, 'split_buf_st, split_buf_size = act_pos * (args.G + WORLD_SIZE), args.G + WORLD_SIZE')
        self.stmt(576, 'dis_splits_buf = split_recv_buf[split_buf_st:split_buf_st + split_buf_size]')
        self.stmt(584, 'combine_send_splits = dis_splits_buf.reshape(WORLD_SIZE, -1)[:, :EXPERTS_PER_RANK].flatten()')
        self.stmt(586, 'num_tokens_from_each_rank = combine_send_splits.reshape(WORLD_SIZE, -1).sum(dim=1).tolist()')
        loop = self.node(589, ast.For)
        self.assertEqual((ast.unparse(loop.target), ast.unparse(loop.iter)), ('ntk', 'num_tokens_from_each_rank'))

        # Base and induction step for the host sum over any number of experts.
        # Its kth partial sum is prefix[k] - prefix[0]. The final metadata
        # word m_st is excluded by the host slice above.
        start, current, following = map(Polynomial.var, ('prefix0', 'prefixK', 'prefixNext'))
        def span(end):
            return value(device_rows, {'m_ed': end, 'm_st': start})
        self.assertEqual(span(start), Polynomial())
        next_difference = value(delta, {'cumsum_sts': current, 'cumsum_eds': following})
        self.assertEqual(span(current) + next_difference, span(following))
        return span(Polynomial.var('prefixEnd'))

    def test_dispatch_dequant_combine_buffers(self):
        self.stmt(462, 'DTYPE = torch.bfloat16')
        self.stmt(515, 'send_buf: torch.Tensor = nvshmem_create_tensor([MAX_NUM_TOKENS, args.N], DTYPE)')
        self.stmt(517, 'recv_buf: torch.Tensor = nvshmem_create_tensor([WORLD_SIZE * MAX_NUM_TOKENS * 2, args.N], DTYPE)')
        before = self.node(552, ast.Call)
        after = self.node(607, ast.Call)
        for call, mode, buffers in [(before, 0, ['scattered_input_cur_rank', 'send_buf', 'recv_buf']),
                                    (after, 1, ['dispatched_tokens', 'recv_buf', 'send_buf'])]:
            self.assertEqual(ast.unparse(call.func), 'all_to_all_kernel[grid]')
            self.assertEqual([ast.unparse(arg) for arg in call.args[:3]], buffers)
            self.assertIn(('MODE', str(mode)), [(kw.arg, ast.unparse(kw.value)) for kw in call.keywords])
        quant = self.node(186, ast.If)
        self.assertEqual(ast.unparse(quant.test), 'ONLINE_QUANT_FP8 and MODE == 0')
        self.stmt(192, 'data_src_ptrs = tl.cast(data_src_ptr, tl.pointer_type(tl.float8e4nv)) + group_offs')
        self.stmt(208, 'tl.store(data_src_ptrs, quant, group_mask)')
        self.stmt(387, 'input_ptrs = tl.cast(input, tl.pointer_type(tl.float8e4nv)) + off_m[:, None] * N + off_n[None, :]')
        self.assertEqual(ast.unparse(self.node(397, ast.Assign).value.args[0].args[0]), 'input_ptrs')
        self.stmt(401, 'deq = (group.to(tl.float32) * scale).to(tl.bfloat16)')
        self.assertEqual(ast.unparse(self.node(402, ast.Expr).value.args[0]), 'out_ptrs')
        self.stmt(426, 'out = torch.empty([m, N * 2], dtype=torch.bfloat16, device=q_tensor.device)')
        self.stmt(427, '_dequant_kernel[grid](out, q_tensor, scales, m, N * 2)')
        self.stmt(428, 'return out')

        # In MODE=1 the BF16 source for the put is the same recv_buf slab
        # freshly written from dequant output. Its former FP8 contents are
        # never loaded. The destination offsets are the dispatch row prefixes.
        self.stmt(148, 'm_st = tl.load(send_splits_cumsum + exp_st)')
        self.stmt(149, 'm_ed = tl.load(send_splits_cumsum + exp_ed)')
        self.stmt(150, 'num_rows_cur_block = m_ed - m_st')
        self.stmt(166, 'tl.store(split_src_ptr + EXPERTS_PER_RANK, m_st)')
        self.stmt(177, 'src_off = pid * MAX_M')
        self.stmt(178, 'dst_off = tl.load(recv_offset + pid)')
        self.stmt(179, 'data_src_ptr = data_src + act_pos * WORLD_SIZE * MAX_M * HIDDEN + src_off * HIDDEN')
        self.stmt(180, 'data_dst_ptr = data_dst + dst_off * HIDDEN')
        self.stmt(219, 'send_tensor_ptrs = send_tensor + m_st * HIDDEN + off_m[:, None] * HIDDEN + off_n[None, :]')
        self.stmt(222, 'data_src_ptrs = data_src_ptr + off_m[:, None] * HIDDEN + off_n[None, :]')
        self.stmt(224, 'data_mask = (off_m[:, None] < num_rows_cur_block - i * BM) & (off_n[None, :] < HIDDEN)')
        self.stmt(226, 'tl.store(data_src_ptrs, tl.load(send_tensor_ptrs, data_mask), data_mask)')
        self.stmt(228, 'send_tensor_ptrs += BM * HIDDEN')
        self.stmt(229, 'data_src_ptrs += BM * HIDDEN')
        self.assertTrue(any(n.lineno == 226 for stmt in quant.orelse for n in ast.walk(stmt)
                            if isinstance(n, ast.Expr)))
        put = self.node(233, ast.Call)
        self.assertEqual(ast.unparse(put.func), 'libshmem_device.putmem_nbi_block')
        self.assertEqual([ast.unparse(x) for x in put.args[:2]], ['data_dst_ptr', 'data_src_ptr'])
        self.stmt(582, 'combine_offset = dis_splits_buf[torch.arange(1, WORLD_SIZE + 1) * (EXPERTS_PER_RANK + 1) - 1]')
        self.stmt(606, 'combine_splits_cumsum = splits_to_cumsum(combine_send_splits)')
        self.assertIn(('recv_offset', 'combine_offset'), [(k.arg, ast.unparse(k.value)) for k in after.keywords])
        self.assertEqual(ast.unparse(after.args[8]), 'combine_splits_cumsum')
        self.stmt(626, 'combined_tokens = send_buf[:scattered_input_cur_rank.shape[0]]')
        for rows in (0, 1, 15, 16, 17, 33):
            for hidden in (128, 384, 7168):
                env = dict(ONLINE_QUANT_FP8=True, MODE=1, HIDDEN=hidden, num_rows_cur_block=rows)
                self.assertEqual(value(put.args[2], env), 2 * rows * hidden)

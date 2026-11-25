"""Symbolic coverage of T04's BF16 combine store and dispatch rank slabs."""
import ast
import unittest

from scripts.census.test_t04_pointer_contract import Polynomial, SOURCE, value


class T04CombineCoverage(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        tree = ast.parse(SOURCE.read_bytes())
        cls.stmts = {n.lineno: n for n in ast.walk(tree) if isinstance(n, ast.stmt)}
        kwargs = next(n for n in ast.walk(tree) if isinstance(n, ast.Dict) and n.lineno == 538)
        cls.launch = {k.value: v for k, v in zip(kwargs.keys, kwargs.values)}

    def expr(self, node, expected):
        self.assertEqual(ast.dump(node), ast.dump(ast.parse(expected, mode='eval').body))

    def nonnegative(self, polynomial):
        # Each monomial in nonnegative independent variables is nonnegative.
        self.assertTrue(all(c >= 0 for c in polynomial.values()), polynomial)

    def test_combine_covers_every_column(self):
        n = Polynomial.var('N')  # stronger than the admissible positive multiples of 128
        env = {'args.N': n}
        hidden = value(self.launch['HIDDEN'], env)
        width = self.launch['BN']
        self.assertEqual(width.lineno, 547)
        if isinstance(width, ast.BinOp) and isinstance(width.op, ast.LShift):
            self.expr(width.left, '1')
            bits = width.right
            self.assertIsInstance(bits, ast.Call)
            self.assertEqual((bits.func.attr, bits.args, bits.keywords), ('bit_length', [], []))
            # For every integer x, x < 2**x.bit_length(). Therefore x+1
            # is a lower bound for the source shift, even when N is zero.
            lower = value(bits.func.value, env) + 1
        else:
            lower = value(width, env)
        self.nonnegative(Polynomial.coerce(lower) - hidden)
        self.expr(width, '1 << (args.N - 1).bit_length()')
        self.assertEqual(ast.unparse(self.stmts[218]), 'off_n = tl.arange(0, BN)')

    def test_combine_rewrites_all_put_rows(self):
        stmts = self.stmts
        self.assertEqual(ast.unparse(stmts[185]), 'off_m = tl.arange(0, BM)')
        self.expr(stmts[186].test, 'ONLINE_QUANT_FP8 and MODE == 0')
        combine = {kw.arg: ast.unparse(kw.value) for kw in stmts[607].value.keywords}
        self.assertEqual((combine['MODE'], combine[None]), ('1', 'kwargs'))
        configs = next(kw.value for kw in stmts[94].decorator_list[0].keywords if kw.arg == 'configs')
        config_kwargs = next(kw.value for kw in configs.elt.keywords if kw.arg == 'kwargs')
        self.expr(config_kwargs, "{'BM': BM}")
        bm_choices = next(g.iter for g in configs.generators if ast.unparse(g.target) == 'BM')
        self.assertTrue(bm_choices.elts and all(isinstance(b, ast.Constant) and b.value > 0 for b in bm_choices.elts))
        self.assertIn(stmts[218], stmts[186].orelse)
        loop = stmts[223]
        self.assertIn(loop, stmts[186].orelse)
        self.assertEqual(ast.unparse(loop.target), 'i')
        self.expr(loop.iter.func, 'tl.range')
        bound, = loop.iter.args
        # For any valid row write row=j*BM+lane (0 <= lane < BM) and
        # rows=row+1+tail. Visiting block j requires bound >= j+1.
        j, lane, tail, bm = map(Polynomial.var, ('block', 'lane', 'tail', 'BM'))
        rows = j * bm + lane + 1 + tail
        if isinstance(bound, ast.Call):
            self.expr(bound, 'ceil_div(num_rows_cur_block, BM)')
            quotient = stmts[79].value
            self.expr(quotient, '(a + b - 1) // b')
            # For positive BM, floor(numerator/BM) >= j+1 iff this gap is nonnegative.
            numerator = value(quotient.left, {'a': rows, 'b': bm})
            gap = numerator - (j + 1) * bm
        else:
            gap = Polynomial.coerce(value(bound, {})) - (j + 1)
        self.nonnegative(gap)
        self.expr(loop.iter, 'tl.range(ceil_div(num_rows_cur_block, BM))')
        self.expr(stmts[224].value, '(off_m[:, None] < num_rows_cur_block - i * BM) & (off_n[None, :] < HIDDEN)')
        self.expr(stmts[226].value, 'tl.store(data_src_ptrs, tl.load(send_tensor_ptrs, data_mask), data_mask)')
        self.assertEqual([s.lineno for s in loop.body], [224, 226, 228, 229])
        self.assertEqual([ast.unparse(s) for s in loop.body[-2:]],
                         ['send_tensor_ptrs += BM * HIDDEN', 'data_src_ptrs += BM * HIDDEN'])
        self.expr(stmts[222].value, 'data_src_ptr + off_m[:, None] * HIDDEN + off_n[None, :]')
        self.assertLess(loop.end_lineno, stmts[233].lineno)
        self.expr(stmts[233].value.args[1], 'data_src_ptr')
        self.assertEqual(value(stmts[233].value.args[2],
                               {'num_rows_cur_block': rows, 'HIDDEN': Polynomial.var('width'),
                                'ONLINE_QUANT_FP8': True, 'MODE': 1}),
                         rows * Polynomial.var('width') * 2)

    def test_dispatch_slab_matches_host_rank_cursor(self):
        stmts = self.stmts
        rank, capacity, pos, world, n, base = map(Polynomial.var, ('r', 'capacity', 'pos', 'world', 'N', 'base'))
        host = {'MAX_NUM_TOKENS': capacity, 'act_pos': pos, 'WORLD_SIZE': world, 'args.N': n}
        dispatch = stmts[552].value
        self.expr(dispatch.args[2], 'recv_buf')
        kwargs = {kw.arg: ast.unparse(kw.value) for kw in dispatch.keywords}
        self.assertEqual([kwargs[k] for k in ('rank', 'act_pos', 'MODE', None)], ['RANK', 'act_pos', '0', 'kwargs'])
        device = {'MAX_M': value(self.launch['MAX_M'], host), 'HIDDEN': value(self.launch['HIDDEN'], host),
                  'WORLD_SIZE': value(self.launch['WORLD_SIZE'], host), 'act_pos': pos, 'data_dst': base}
        dest = stmts[170].value
        self.expr(dest, 'rank * MAX_M')
        self.expr(stmts[172].value, 'data_dst + act_pos * WORLD_SIZE * MAX_M * HIDDEN + dst_off * HIDDEN')
        self.assertEqual(ast.dump(stmts[588]), ast.dump(ast.parse('off, token_vec, scale_vec = 0, [], []').body[0]))
        loop = stmts[589]
        self.expr(loop.iter, 'num_tokens_from_each_rank')
        self.assertIs(loop.body[-1], stmts[597])
        self.assertEqual(ast.unparse(stmts[597]), 'off += MAX_NUM_TOKENS')

        def rank_offset(r):
            return Polynomial.coerce(value(dest, {**device, 'rank': r}))

        # The host cursor starts at rank zero; advancing once agrees with r -> r+1.
        self.assertEqual(rank_offset(0), Polynomial.constant(stmts[588].value.elts[0].value))
        self.assertEqual(rank_offset(rank) + value(stmts[597].value, host), rank_offset(rank + 1))
        device_ptr = value(stmts[172].value, {**device, 'dst_off': rank_offset(rank)})
        self.expr(stmts[578].value, 'recv_buf[data_buf_st:data_buf_st + data_buf_size, :]')
        slab_start = value(stmts[574].value.elts[0], host)
        self.assertEqual(device_ptr, base + (slab_start + rank_offset(rank)) * n)

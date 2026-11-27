"""Generate the heterogeneous file-runner examples from independent scalar formulas."""
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import struct
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from interp.tensorfile import Tensor

DATA = HERE / "tensor_examples"
SPECS = ROOT / "experiments/interp_gpu/specs/examples"
ARTIFACTS = {}


def bf16(x):
    """Round a finite binary64 input directly to bfloat16, ties to even."""
    if x == 0:
        return 0x8000 if math.copysign(1, x) < 0 else 0
    magnitude = Fraction(abs(x))
    exponent = max(-126, math.frexp(abs(x))[1] - 1)
    significand = round(magnitude / Fraction(2) ** (exponent - 7))
    bits = significand + ((exponent + 126) << 7)
    return bits | (0x8000 if x < 0 else 0)


def data(name, dtype, shape, values):
    if len(values) != math.prod(shape):
        raise ValueError(f"{name}: shape {shape} has {len(values)} values")
    raw = (struct.pack(f"<{len(values)}H", *(bf16(x) for x in values)) if dtype == "bf16"
           else struct.pack(f"<{len(values)}{'f' if dtype == 'fp32' else 'd'}", *values))
    path = DATA / (name + ".tensor")
    artifact(path, Tensor(dtype, tuple(shape), raw).to_bytes())
    return {"dtype": dtype, "shape": shape, "file": str(path.relative_to(ROOT))}


def example(name, family, lean, python, grid, constants, arguments, inputs, outputs):
    spec = {
        "version": 1,
        "kernel": {"name": name, "lean": f"VeriTile.Bench.Examples.{family}.Kernels.{lean}",
                   "source": f"bench/examples/{family}/{family}.py::{python}"},
        "grid": [grid], "launch": {"carrier": "binary64"}, "constexpr": constants,
        "arguments": [{"parameter": a, "buffer": a} if isinstance(a, str)
                      else {"parameter": a[0], "value": a[1]} for a in arguments],
        "input_classes": [{"class": "normal", "inputs": inputs,
                           "expected": {k: t["file"] for k, t in outputs.items()}}],
        "output_buffers": [{"name": k, "dtype": t["dtype"], "shape": t["shape"]}
                           for k, t in outputs.items()],
    }
    artifact(SPECS / (name + ".json"), (json.dumps(spec, ensure_ascii=False, indent=2) + "\n").encode())


def build_adam():
    p, grad, avg = [1, -2, 3, 4, -5], [1, -1, .25, -1, 0], [1, -1, -.25, 3, 0]
    lr, wd, b1, b2 = .25, .125, .5, .75
    inputs = {k: data("adam-" + k, "fp32", [5], xs)
              for k, xs in zip(("p_ptr", "grad_ptr", "exp_avg_ptr"), (p, grad, avg))}
    update = [b1 * m + (1 - b1) * g for g, m in zip(grad, avg)]
    final_p = [x * (1 - lr * wd) - lr * ((d > 0) - (d < 0)) for x, d in zip(p, update)]
    final_m = [b2 * m + (1 - b2) * g for m, g in zip(avg, grad)]
    outputs = {"p_ptr": data("adam-params", "fp32", [5], final_p),
               "exp_avg_ptr": data("adam-momentum", "fp32", [5], final_m)}
    example("AdamUpdateGridLaunch", "AdamUpdateGridLaunch", "update_fn_kernel", "update_fn_kernel",
            2, {"BLOCK_SIZE": 4}, [*inputs, ("lr", lr), ("wd", wd), ("beta1", b1),
                                  ("beta2", b2), ("n_elements", 5), ("chunk_elements", 5)], inputs, outputs)


def build_rows():
    rows = [[-6., -4., -7., -2.], [1., 4., -3., 2.]]
    flat = [x for row in rows for x in row]
    x = data("row-matrix", "fp32", [2, 4], flat)
    for name, op, source, lean in [("RowWiseMax", max, "row_wise_max", "rowWiseMaxKernel"),
                                    ("RowWiseSum", sum, "row_wise_sum", "rowWiseSumKernel")]:
        example(name, name, lean,
                source, 2, {"nCol": 4, "blockSize": 4}, ["xReg", "yReg"], {"xReg": x},
                {"yReg": data(name, "fp32", [2], list(map(op, rows)))})
    gamma, beta, eps = [1, -2, .5, 2], [0, 1, -.25, .5], .125
    normalized = []
    for row in rows:
        mean = sum(row) / len(row)
        var = sum((v - mean) ** 2 for v in row) / len(row)
        normalized.extend((v - mean) / math.sqrt(var + eps) * g + b for v, g, b in zip(row, gamma, beta))
    example("FusedLayerNorm", "FusedLayerNorm", "fusedLayerNormKernel", "fusedLayerNormKernel",
            2, {"N": 4, "ε": eps}, ["xReg", "γReg", "βReg", "yReg", ("rowStride", 5)],
            {"xReg": data("norm-padded", "fp32", [2, 5], rows[0]+[1000]+rows[1]+[-1000]),
             "γReg": data("norm-scale", "fp32", [4], gamma), "βReg": data("norm-bias", "fp32", [4], beta)},
            {"yReg": data("norm-output", "bf16", [2, 4], normalized)})
    row = rows[0]
    mean = sum(row) / len(row)
    var = sum((v - mean) ** 2 for v in row) / len(row)
    example("Welford", "Welford", "onlineWelfordKernel", "onlineWelfordKernel", 1, {"blockSize": 4},
            ["xReg", "meanReg", "varReg", ("rowStride", 5)],
            {"xReg": data("welford-row", "fp32", [1, 5], row + [100])},
            {"meanReg": data("welford-mean", "bf16", [1], [mean]), "varReg": data("welford-var", "bf16", [1], [var])})


def build_silu():
    x, gate, residual = [1, 2, -1, .5], [-1, 1, 2, .5], [1, -2, .25, 3]
    product = [a * b for a, b in zip(x, gate)]
    activation = [z / (1 + math.exp(-z)) for z in product]
    result = [a + b for a, b in zip(residual, activation)]
    tensors = {p: data("silu-" + p, "bf16" if p == "outReg" else "fp64", [4], vals)
               for p, vals in zip(("xReg","gateReg","residualReg","zReg","siluReg","outReg"),
                                  (x, gate, residual, product, activation, result))}
    for name, lean, source, ins, out in [
        ("FusedSiLU", "fusedSiLUKernel", "fused_silu", ["xReg","gateReg","residualReg"], "outReg"),
        ("FusedSiLUGate", "siluStepGateKernel", "silu_gate", ["xReg","gateReg"], "zReg"),
        ("FusedSiLUActivation", "siluStepSiluKernel", "silu_activation", ["zReg"], "siluReg"),
        ("FusedSiLUResidual", "siluStepResidualKernel", "silu_residual", ["siluReg","residualReg"], "outReg"),
    ]:
        example(name, "FusedSiLU", lean, source, 2, {"blockSize": 2}, [*ins,out],
                {key: tensors[key] for key in ins}, {out: tensors[out]})


def normalized_weights(logits, rows, cols, tau, iters):
    """Balance positive matrix entries directly, independent of the log-domain kernel."""
    matrix = [[math.exp(logits[i*cols+j] / tau) for j in range(cols)] for i in range(rows)]
    for _ in range(iters):
        matrix = [[x / sum(row) for x in row] for row in matrix]
        totals = list(map(sum, zip(*matrix)))
        matrix = [[x / col for x, col in zip(row, totals)] for row in matrix]
    return matrix


def build_hyper():
    B, S, T, D, iters, tau = 2, 2, 4, 2, 2, 2
    dims = {"S": S, "T": T, "D": D, "numIters": iters}
    res = [1,3,-1,4,2,-3,5,.5]
    branch = [-1,3,5,.5,-2,1,.25,2,1,2,3,4,-1,-3,2,7]
    post = [-2,1,0,2,1,-1,-1,2]
    hres, hpre = [-1,2,1,0], [2,1,-1,0,1,-2,0,2]
    res_input = data("hyper-res", "fp32", [B,S,D], res)
    post_w = normalized_weights(post,T,S,tau,iters)
    depth = [res[(b*S+s)*D+d] + sum(post_w[t][s]*branch[(b*T+t)*D+d] for t in range(T))
             for b in range(B) for s in range(S) for d in range(D)]
    example("HyperConnectionsDepth", "HyperConnectionsDepth", "matrixKernel","matrixKernel",B,dims,
            ["resMixReg","branchOutReg","hPostReg","outReg",("tau",tau)],
            {"resMixReg": res_input,"branchOutReg": data("hyper-branch","fp32",[B,T,D],branch),
             "hPostReg": data("hyper-post","fp32",[T,S],post)},
            {"outReg": data("hyper-depth","fp32",[B,S,D],depth)})
    res_w, pre_w = normalized_weights(hres,S,S,tau,iters), normalized_weights(hpre,S,T,tau,iters)
    mix = [sum(res_w[s][k]*res[(b*S+k)*D+d] for k in range(S)) for b in range(B) for s in range(S) for d in range(D)]
    branch_in = [sum(pre_w[k][t]*res[(b*S+k)*D+d] for k in range(S)) for b in range(B) for t in range(T) for d in range(D)]
    example("HyperConnectionsWidth","HyperConnectionsWidth","matrixKernel","matrixKernel",B,dims,
            ["resReg","hResReg","hPreReg","resMixReg","branchInReg",("tau",tau)],
            {"resReg":res_input,"hResReg":data("hyper-res-logits","fp32",[S,S],hres),
             "hPreReg":data("hyper-pre","fp32",[S,T],hpre)},
            {"resMixReg":data("hyper-mix","fp32",[B,S,D],mix),"branchInReg":data("hyper-in","fp32",[B,T,D],branch_in)})
    a, b, h = [2,-3], [1,4], .5
    example("HyperConnectionsDepthScalar","HyperConnectionsDepth","scalarKernel","scalarKernel",B,{},
            ["resMixReg","branchOutReg","hPostReg","outReg",("tau",tau)],
            {"resMixReg":data("hyper-scalar-res","fp32",[B],a),"branchOutReg":data("hyper-scalar-branch","fp32",[B],b),
             "hPostReg":data("hyper-scalar-post","fp32",[1],[h])},
            {"outReg":data("hyper-scalar","fp32",[B],[v+math.exp(h/tau)*w for v,w in zip(a,b)])})


def artifact(path, content):
    if path in ARTIFACTS:
        raise ValueError(f"duplicate artifact {path}")
    ARTIFACTS[path] = content


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--check", action="store_true")
    args = cli.parse_args()
    build_adam()
    build_rows()
    build_silu()
    build_hyper()
    for path, content in ARTIFACTS.items():
        if args.check:
            if not path.is_file() or path.read_bytes() != content:
                raise SystemExit(f"incorrect independent fixture or specification: {path}")
        else:
            path.parent.mkdir(exist_ok=True, parents=True)
            path.write_bytes(content)

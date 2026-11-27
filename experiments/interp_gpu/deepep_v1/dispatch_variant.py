"""Materialize the pinned DeepEP v1 original and the seven-site dispatch variant side by side."""
import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

PIN = '9ba8a605d347f600a95d0275e2639cb00122c084'
SOURCE_RECORD = 'deepep-source-sha256 '  # Captured in the bundle stdout.log of this repeat.
PORT = 'examples/distributed/deepseek_deepep'
HERE = Path(__file__).resolve().parent
KERNELS = {
    'dispatch_kernel': ('dispatch', (2, 24, 256, 64, 2, 8, 20)),
    'cached_dispatch_kernel': ('dispatch', (2, 40, 24, 256, 64, 20)),
    'combine_kernel': ('combine', (2, 10, 256, 64, 2, 20)),
}


def materialize(checkout, destination):
    """Read tracked objects at the pin, including all the port's imported modules."""
    checkout, destination = Path(checkout), Path(destination)
    git = ['git', '-C', str(checkout)]
    head = subprocess.check_output([*git, 'rev-parse', 'HEAD'], text=True).strip()
    if head != PIN:
        raise ValueError(f'TileScale checkout is {head}, expected {PIN}')
    src, patched = destination / 'original', destination / 'dispatch-release'
    src.mkdir(parents=True)
    tree = f'{PIN}:{PORT}'
    paths = subprocess.check_output([*git, 'ls-tree', '-r', '--name-only', tree], text=True).splitlines()
    for name in paths:
        out = src / name
        out.parent.mkdir(exist_ok=True, parents=True)
        out.write_bytes(subprocess.check_output([*git, 'show', f'{tree}/{name}']))
    shutil.copytree(src, patched)
    # --no-index also works when the caller chooses a destination inside another checkout.
    subprocess.run(['git', 'apply', '--no-index', str(HERE / 'dispatch-release.patch')], cwd=patched, check=True,
                   env={**os.environ, 'GIT_CEILING_DIRECTORIES': str(patched.resolve().parent)})
    return src, patched


def run(rank, ranks, inputs, outputs, launch):
    """GPU rank entry; resolve the import root once per fresh gpurun rank process."""
    from gpurun import dist
    from gpurun.run import load_entry
    port = dist.deepep_port()
    if port is None:
        raise ValueError('the editable TileScale checkout is required')
    # Python caches these global names. Refuse a process that already imported an original.
    names = {'buffer', 'deepep_utils', 'intranode', 'internode'}
    if any(name.split('.')[0] in names for name in sys.modules):
        raise ValueError('DeepEP modules already loaded before variant selection')
    run_port = load_entry('experiments/interp_gpu/deepep_v1/harness.py::run_port', HERE.parents[2])
    with tempfile.TemporaryDirectory(prefix='deepep-rank-') as tmp:
        _, patched = materialize(port.parents[2], tmp)
        files = {path.relative_to(patched).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in patched.rglob('*.py')}
        sys.stdout.write(SOURCE_RECORD + json.dumps({'rank': rank, 'files': files}, sort_keys=True) + '\n')
        sys.stdout.flush()
        run_port(patched, rank, ranks, inputs, outputs, launch, verify_origin=True)


def compile_device(port, name, destination):
    """Compile a full port kernel and retain nvcc's generated CUDA input; launch nothing."""
    from tilelang import tvm
    from tilelang.engine import lower
    module, args = KERNELS[name]
    sys.path.insert(0, str(port))
    kernel = getattr(importlib.import_module('intranode.' + module), name)
    target = tvm.target.Target('cuda -arch=sm_90')
    with target, tvm.transform.PassContext(opt_level=3, config=kernel.pass_configs):
        artifact = lower(kernel.get_tir(*args), target=target, enable_device_compile=True)
    destination.write_text(artifact.kernel_source)


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    commands = cli.add_subparsers(dest='action', required=True)
    build = commands.add_parser('materialize')
    build.add_argument('checkout', type=Path)
    build.add_argument('destination', type=Path)
    compile_cli = commands.add_parser('compile')
    compile_cli.add_argument('port', type=Path)
    compile_cli.add_argument('kernel', choices=KERNELS)
    compile_cli.add_argument('cuda_output', type=Path)
    args = cli.parse_args()
    if args.action == 'materialize':
        for path in materialize(args.checkout, args.destination):
            print(path)
    else:
        compile_device(args.port, args.kernel, args.cuda_output)

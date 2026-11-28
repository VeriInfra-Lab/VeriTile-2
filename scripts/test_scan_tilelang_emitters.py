import contextlib
import csv
import io
import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts import scan_tilelang_emitters as reverse


class ReverseInstructions(unittest.TestCase):
    def test_lexical_owners_include_specializations_and_split_mnemonics(self):
        source = r'''
        // asm("wgmma.fence");
        const char *diagnostic = "tcgen05.mma";
        template<class T> struct Dense;
        template<> struct Dense<int> {
          __device__ static void run() {
            asm volatile("{\n\t" "wgm" "ma.fence.sync.aligned;}");
            cute::warpgroup_wait<3>();
            asm(R"ptx(tcgen05.wait::ld.sync.aligned;)ptx");
          }
        };
        TL_DEVICE void wrapper() { Dense<int>::run(); }
        '''
        self.assertEqual(reverse.emitters("sample.h", source), {
            reverse.Function("sample.h", 6, "Dense<int>::run"):
                {"wgmma.fence.sync.aligned", "cute::warpgroup_wait", "tcgen05.wait::ld.sync.aligned"},
        })

    def test_enum_operand_is_not_an_emission(self):
        text = "TL_DEVICE void x() { auto s = cute::SM90::GMMA::ScaleOut::One; }"
        self.assertEqual(reverse.emitters("sample.h", text), {})
        # Conversely a concrete CUTLASS FMA call and the asynchronous fence both count.
        code = 'TL_DEVICE void x() { cute::SM90_64x8x16_F32F16F16_SS::fma(a); asm("fence.proxy.async;"); }'
        self.assertEqual(next(iter(reverse.emitters("sample.h", code).values())),
                         {"cute::SM90::GMMA::fma", "fence.proxy.async"})

    def test_macro_assembly_template_fails(self):
        for operand in ('OPCODE', '"{" OPCODE "}"'):
            with self.subTest(operand=operand), self.assertRaisesRegex(ValueError, 'sample.h:2: unsupported asm template'):
                reverse.emitters('sample.h', '#define OPCODE "wgmma.fence;"\nTL_DEVICE void x() { asm(' + operand + '); }')

    def test_unqualified_warpgroup_call_fails(self):
        with self.assertRaisesRegex(ValueError, 'sample.h:2: unsupported call: warpgroup_wait'):
            reverse.emitters('sample.h', 'using namespace cute;\nTL_DEVICE void x() { warpgroup_wait<2>(); }')

    def test_cutlass_fence_call_fails(self):
        with self.assertRaisesRegex(ValueError, 'sample.h:1: unsupported call: cutlass::arch::fence_view_async_shared'):
            reverse.emitters('sample.h', 'TL_DEVICE void x() { cutlass :: arch :: fence_view_async_shared(); }')

    def test_unqualified_sm90_fma_fails(self):
        with self.assertRaisesRegex(ValueError, 'sample.h:1: unsupported call: SM90_Example'):
            reverse.emitters('sample.h', 'TL_DEVICE void x() { SM90_Example<int>::fma(a); }')

    def test_conditional_assembly_literals_scan_both_paths(self):
        source = 'TL_DEVICE void x() { asm("wg"\n#if USE_FENCE\n"mma.fence"\n#else\n"mma.wait_group"\n#endif\n";"); }'
        self.assertEqual(reverse.emitters('sample.h', source), {
            reverse.Function('sample.h', 1, 'x'): {'wgmma.fence', 'wgmma.wait_group'},
        })

    def test_internal_route_requires_a_reason(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'exports.tsv').write_text('export\nunused\n')
            fixture = root / 'instruction_emitters.tsv'
            fixture.write_text('\t'.join(reverse.HEADER) + '\n' + 'device.h\t1\tworker\ttcgen05.fence\tlocal\n')
            route = root / 'instruction_routes.tsv'
            header = 'route\texports\temitters\treason\tsource_witnesses\n'
            route.write_text(header + 'local\tinternal\tdevice.h:worker\tdevice-only helper\tdevice.h:1:worker\n')
            self.assertEqual(reverse.check(None, fixture, allowed_exports=set()), 1)
            route.write_text(header + 'local\tinternal\tdevice.h:worker\t  \tdevice.h:1:worker\n')
            with self.assertRaisesRegex(ValueError, 'unexplained route'):
                reverse.check(None, fixture, allowed_exports=set())

    def test_complete_git_tree_and_unmapped_emitter(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            repo = root / "repo"
            repo.mkdir()
            def git(*args):
                return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()
            git("init", "-q")
            template = repo / reverse.TEMPLATES / "device.h"
            template.parent.mkdir(parents=True)
            template.write_text('TL_DEVICE void mapped() { asm("tcgen05.fence;"); }\n')
            def commit():
                git("add", ".")
                git("-c", "user.name=test", "-c", "user.email=fixture@example.invalid",
                    "commit", "-qm", "source fixture")
                return git("rev-parse", "HEAD")
            pin = commit()

            fixture = root / "instruction_emitters.tsv"
            def put(path, rows):
                with path.open("w", newline="") as stream:
                    csv.writer(stream, delimiter="\t", lineterminator="\n").writerows(rows)
            put(root / "exports.tsv", [("export",), ("mapped",)])
            put(root / "instruction_routes.tsv", [
                ("route", "exports", "emitters", "reason", "source_witnesses"),
                ("mapped", "mapped", "device.h:mapped", "test entry point",
                 reverse.TEMPLATES + "/device.h:1:void mapped()"),
            ])
            put(fixture, [reverse.HEADER, ("device.h", 1, "mapped", "tcgen05.fence", "mapped")])
            args = ["--sources", str(repo), "--check"]
            with contextlib.redirect_stdout(io.StringIO()):
                reverse.main(args, fixture=fixture, pin=pin)

            added = template.with_name("new_cuda_header.h")
            added.write_text('template<int N> TL_DEVICE void unclassified() { asm("wgmma.fence;"); }\n')
            changed = commit()
            with contextlib.redirect_stderr(io.StringIO()) as result, self.assertRaises(SystemExit) as error:
                reverse.main(args, fixture=fixture, pin=changed)
            self.assertEqual(error.exception.code, 1)
            self.assertIn("unmapped emitter: new_cuda_header.h:1: unclassified", result.getvalue())
            with contextlib.redirect_stdout(io.StringIO()):
                reverse.main(args, fixture=fixture, pin=pin)

            # Check each future source through the same command as a pin-bump rescan.
            for expression, diagnostic in (
                ('asm(OPCODE)', 'unsupported asm template'),
                ('warpgroup_arrive()', 'unsupported call: warpgroup_arrive'),
                ('SM90_Example::fma(a)', 'unsupported call: SM90_Example'),
                ('cutlass::arch::fence_view_async_shared()', 'unsupported call: cutlass::arch::fence'),
            ):
                with self.subTest(expression=expression):
                    added.write_text('#define OPCODE "wgmma.fence;"\n'
                                     f'TL_DEVICE void x() {{ {expression}; }}\n')
                    changed = commit()
                    with contextlib.redirect_stderr(io.StringIO()) as result, self.assertRaises(SystemExit) as error:
                        reverse.main(args, fixture=fixture, pin=changed)
                    self.assertEqual(error.exception.code, 1)
                    self.assertIn('new_cuda_header.h:2: ' + diagnostic, result.getvalue())

            with self.assertRaisesRegex(ValueError, "no excluded or kept disposition"):
                reverse.check(None, fixture, allowed_exports=set())

            put(root / "exports.tsv", [("export",), ("other",)])
            with self.assertRaisesRegex(ValueError, "unknown export"):
                reverse.check(None, fixture)


if __name__ == "__main__":
    unittest.main()

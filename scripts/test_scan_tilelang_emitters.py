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

            put(root / "exports.tsv", [("export",), ("other",)])
            with self.assertRaisesRegex(ValueError, "unknown export"):
                reverse.check(None, fixture)


if __name__ == "__main__":
    unittest.main()

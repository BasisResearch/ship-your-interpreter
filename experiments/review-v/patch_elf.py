"""Build a corpus ELF from the proof ELF by overwriting the script blob at
_script_start with the given script padded with newlines to the proof
script's length (453) plus its NUL. Every other byte is unchanged."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
# Built ELFs and traces live outside the repository (CLAUDE.md, Documentation).
WORK = os.environ.get("REVIEW_V_WORK", "/tmp/review-v-work")
sys.path.insert(0, ROOT + "/scripts")
from difftest import elf_symbols
from difftest_lib import Image
PROOF = ROOT + "/c/while-riscv-htif.elf"
REFLEN = 453
def build(script_path, out_path):
    img = Image(PROOF)
    syms = elf_symbols(img)
    start = syms["_script_start"]
    src = open(script_path, "rb").read()
    if len(src) > REFLEN:
        raise SystemExit(f"{script_path}: {len(src)} bytes exceeds capacity {REFLEN}")
    padded = src + b"\n" * (REFLEN - len(src))
    raw = bytearray(img.raw)
    v, off, sz = img.segs[0]
    assert v <= start < v + sz
    fo = off + (start - v)
    assert raw[fo + REFLEN] == 0, "expected NUL after the proof script"
    raw[fo:fo + REFLEN] = padded
    open(out_path, "wb").write(raw)
    # verify: only the script bytes differ
    diff = [i for i in range(len(raw)) if raw[i] != img.raw[i]]
    assert all(fo <= i < fo + REFLEN for i in diff), "non-script byte changed"
    return len(src), len(diff)
if __name__ == "__main__":
    for p in sys.argv[1:]:
        n = os.path.splitext(os.path.basename(p))[0]
        out = os.path.join(WORK, "elfs", n + ".elf")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        print(n, build(p, out))

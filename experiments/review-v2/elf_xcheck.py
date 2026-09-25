# Independent cross-check (pure Python, no Lean): the on-disk ELF, the embedded elfHex,
# the generated fixed image (FixedImageData.lean), the loader image (ImageData.lean),
# and the PT_LOAD segments of the ELF.
import re, struct, hashlib, sys
import os
root = os.environ.get("VSA_ROOT", os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))
raw = open(root + "/c/while-riscv-htif.elf", "rb").read()
print("elf sha256", hashlib.sha256(raw).hexdigest(), "len", len(raw))
hx = re.search(r'def elfHex : String :=\s*"([0-9a-f]+)"', open(root + "/Vsa/ElfBytes.lean").read()).group(1)
print("elfHex bytes == file:", bytes.fromhex(hx) == raw, len(hx)//2)
# program headers
phoff = struct.unpack_from("<Q", raw, 32)[0]; phentsize, phnum = struct.unpack_from("<HH", raw, 54)
segs = []
for i in range(phnum):
    p_type, p_flags, p_offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_align = struct.unpack_from("<IIQQQQQQ", raw, phoff + i*phentsize)
    segs.append((p_type, p_flags, p_offset, p_vaddr, p_filesz, p_memsz))
    print(f"PH type={p_type:#x} flags={p_flags} off={p_offset:#x} vaddr={p_vaddr:#x} filesz={p_filesz} memsz={p_memsz}")
e_flags = struct.unpack_from("<I", raw, 48)[0]; print("e_flags", hex(e_flags), "(RVC bit set)" if e_flags & 1 else "(no RVC)")
# section headers
shoff = struct.unpack_from("<Q", raw, 40)[0]; shentsize, shnum, shstrndx = struct.unpack_from("<HHH", raw, 58)
shdrs = [struct.unpack_from("<IIQQQQIIQQ", raw, shoff + i*shentsize) for i in range(shnum)]
strtab = shdrs[shstrndx]; names = raw[strtab[4]:strtab[4]+strtab[5]]
covered = []  # (file offset, size) of sections+headers
for h in shdrs:
    nm = names[h[0]:names.index(b"\0", h[0])].decode()
    if h[1] != 8 and h[5]: covered.append((h[4], h[5]))
    print(f"SH {nm:20s} type={h[1]} addr={h[3]:#x} off={h[4]:#x} size={h[5]}")
# generated packed pages
def pages(path, name):
    txt = open(path).read()
    pg = {int(m.group(1)): int(m.group(2), 16) for m in re.finditer(rf'def {name}Page(\d+) : Nat := 0x([0-9a-f]+)', txt)}
    out = bytearray()
    for i in range(len(pg)):
        v = pg[i]; out += v.to_bytes(256, "little")
    return bytes(out)
text = pages(root + "/Vsa/Sim/Code/FixedImageData.lean", "fixedText")
rod = pages(root + "/Vsa/Sim/Code/FixedImageData.lean", "fixedRodata")
data = pages(root + "/Vsa/Sim/Boot/ImageData.lean", "bootDataByte")
def filebytes(vaddr, n):
    for t, f, off, va, fsz, msz in segs:
        if t == 1 and va <= vaddr and vaddr + n <= va + fsz:
            return raw[off + (vaddr - va): off + (vaddr - va) + n]
    raise SystemExit(f"not in a PT_LOAD filesz: {vaddr:#x}+{n}")
TEXT, TEXTN = 0x80000000, 101344; ROD, RODN = 0x80018be0, 8464; DATA = 0x8001acf0
print("fixedText pages bytes", len(text), "== file .text:", text[:TEXTN] == filebytes(TEXT, TEXTN), "pad zero:", not any(text[TEXTN:]))
print("fixedRodata bytes", len(rod), "== file .rodata:", rod[:RODN] == filebytes(ROD, RODN), "pad zero:", not any(rod[RODN:]))
seg = [s for s in segs if s[0] == 1 and s[3] == 0x80000000][0]
datan = seg[4] - (DATA - 0x80000000)
print("bootData bytes", len(data), "expected", datan, "== file:", data[:datan] == filebytes(DATA, datan), "pad zero:", not any(data[datan:]))
print("script blob (453) at 0x80018be0:", filebytes(ROD, 453)[:40], "... NUL at +453:", filebytes(ROD+453, 1))
print("script == c/tests/while.wl padded with \\n:", filebytes(ROD, 453) == open(root+"/c/tests/while.wl","rb").read().ljust(453, b"\n"))
img = open(root + "/Vsa/Sim/Boot/ImageData.lean").read()
print("bootPieces:", re.search(r'def bootPieces.*?\n\s*(\[.*?\])', img, re.S).group(1))
lows = {int(m.group(1)): int(m.group(2), 16) for m in re.finditer(r'def bootLow(\d+) : Nat := 0x([0-9a-f]+)', img)}
# low pieces are file regions ELFSage did not attribute to sections: check they equal file bytes at those *file offsets*
for base, n, i in [(0x0, 28, 0), (0xe8, 3864, 1), (0x21b7d, 3, 2)]:
    b = lows[i].to_bytes(n, "little")
    print(f"bootLow{i} at file offset {base:#x} == file bytes:", b == raw[base:base+n])
# segment(s) not loaded
for t, f, off, va, fsz, msz in segs:
    if t == 1: print(f"PT_LOAD vaddr={va:#x} filesz={fsz} memsz={msz} -> bss (not loaded) = {msz-fsz} bytes [{va+fsz:#x},{va+msz:#x})")

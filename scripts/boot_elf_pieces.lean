import LeanRiscv
/-! Dump the pieces `initializeMemory .B64` inserts for each ELF argument, in
insertion order (interpreted segments, then bits-and-bobs), as TSV lines
`<path>\t<kind>\t<base>\t<hex bytes>`. Consumed by `scripts/gen_boot_witness.py`,
which checks them against the generated loader image. Run:
`lake env lean --run scripts/boot_elf_pieces.lean <elf>...` -/
open LeanRV64DExecutable

def hexOf (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ (if x < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 x.toNat)) ""

def main (args : List String) : IO UInt32 := do
  for path in args do
    let bytes ← IO.FS.readBinFile path
    match mkRawELFFile? bytes with
    | .ok (.elf64 elf) =>
      for (_, s) in elf.interpreted_segments do
        IO.println s!"{path}\tseg\t{s.segment_base}\t{hexOf s.segment_body}"
      for (a, d) in elf.bits_and_bobs do
        IO.println s!"{path}\tbob\t{a}\t{hexOf d}"
    | _ =>
      IO.eprintln s!"{path}: not a 64-bit ELF"
      return 1
  return 0

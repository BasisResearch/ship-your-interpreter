import Vsa.Compiler.CorrectG

namespace Vsa.Compiler

def readLE (b : ByteArray) (off n : Nat) : Nat :=
  (List.range n).foldr (fun i acc => acc * 256 + (b.get! (off + i)).toNat) 0

def writeLE (b : ByteArray) (off n v : Nat) : ByteArray :=
  (List.range n).foldl (fun b i => b.set! (off + i) (UInt8.ofNat (v / 256 ^ i % 256))) b

def patchImage (base code : ByteArray) (addr : Nat) : Except String ByteArray := do
  unless base.size ≥ 64 && base.get! 0 == 0x7f && base.get! 1 == 0x45 && base.get! 2 == 0x4c &&
      base.get! 3 == 0x46 && base.get! 4 == 2 && base.get! 5 == 1 do
    throw "the base image is not a little-endian ELF64 file"
  let phoff := readLE base 0x20 8
  let phentsize := readLE base 0x36 2
  let phnum := readLE base 0x38 2
  let seg := (List.range phnum).find? fun i =>
    let h := phoff + i * phentsize
    readLE base h 4 == 1 && readLE base (h + 16) 8 ≤ addr &&
      addr + code.size ≤ readLE base (h + 16) 8 + readLE base (h + 32) 8
  match seg with
  | none => throw "no loadable segment of the base image covers the code"
  | some i =>
    let h := phoff + i * phentsize
    let off := readLE base (h + 8) 8 + (addr - readLE base (h + 16) 8)
    let img := (List.range code.size).foldl (fun b k => b.set! (off + k) (code.get! k)) base
    return writeLE img 0x18 8 addr

def buildImage (base : ByteArray) (p : Vsa.While.Program) : Except String ByteArray :=
  patchImage base ⟨(compileGBytes p).toArray.map (·.toNat.toUInt8)⟩ codeBase

end Vsa.Compiler

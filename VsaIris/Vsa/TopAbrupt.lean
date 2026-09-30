import VsaIris.Vsa.Landing
import VsaIris.Vsa.Oom

namespace VsaIris.Newlib.TopAbrupt

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Newlib.Sites VsaIris.Newlib.Exit
  VsaIris.Newlib.MainErr VsaIris.Newlib.Landing

structure TopSite where
  head : Nat
  fmt : BitVec 64
  fmtBytes : List (BitVec 8)
  jal : JalSite

structure TopSite.OK (T : TopSite) : Prop where
  jalCert : T.jal.Cert
  jalTgt : T.jal.tgt = snprintfEntry
  jalText : TextAt T.jal.pc T.jal.code
  fmtText : ∀ i (h : i < T.fmtBytes.length), rodataDom (T.fmt.toNat + i) ∧
    rodataByte (T.fmt.toNat + i) = T.fmtBytes[i] ∧ T.fmtBytes[i] ≠ 0
  fmtNul : rodataDom (T.fmt.toNat + T.fmtBytes.length) ∧
    rodataByte (T.fmt.toNat + T.fmtBytes.length) = 0
  fmtParse : parseFmt T.fmtBytes = some [.int]

theorem fmt_ok {T : TopSite} (hT : T.OK) (lv : BitVec 64) :
    FmtArgsOK (fun a => rodataDom a ∨ False) rodataByte T.fmt [lv] := by
  refine ⟨T.fmtBytes, [.int], ⟨cstrCov_rodata (fun a ha => ⟨.inl ha, rfl⟩) hT.fmtText hT.fmtNul,
    hT.fmtParse, by simp, ?_⟩⟩
  intro i hi hs
  have : i = 0 := by simpa using hi
  subst this
  simp at hs

def topRetFmtBytes : List (BitVec 8) := [0x72#8, 0x75#8, 0x6e#8, 0x74#8, 0x69#8, 0x6d#8, 0x65#8, 0x20#8, 0x65#8, 0x72#8, 0x72#8, 0x6f#8, 0x72#8, 0x20#8, 0x5b#8, 0x6c#8, 0x69#8, 0x6e#8, 0x65#8, 0x20#8, 0x25#8, 0x64#8, 0x5d#8, 0x3a#8, 0x20#8, 0x27#8, 0x72#8, 0x65#8, 0x74#8, 0x75#8, 0x72#8, 0x6e#8, 0x27#8, 0x20#8, 0x6f#8, 0x75#8, 0x74#8, 0x73#8, 0x69#8, 0x64#8, 0x65#8, 0x20#8, 0x6f#8, 0x66#8, 0x20#8, 0x61#8, 0x20#8, 0x66#8, 0x75#8, 0x6e#8, 0x63#8, 0x74#8, 0x69#8, 0x6f#8, 0x6e#8]

def topBrkFmtBytes : List (BitVec 8) := [0x72#8, 0x75#8, 0x6e#8, 0x74#8, 0x69#8, 0x6d#8, 0x65#8, 0x20#8, 0x65#8, 0x72#8, 0x72#8, 0x6f#8, 0x72#8, 0x20#8, 0x5b#8, 0x6c#8, 0x69#8, 0x6e#8, 0x65#8, 0x20#8, 0x25#8, 0x64#8, 0x5d#8, 0x3a#8, 0x20#8, 0x27#8, 0x62#8, 0x72#8, 0x65#8, 0x61#8, 0x6b#8, 0x27#8, 0x2f#8, 0x27#8, 0x63#8, 0x6f#8, 0x6e#8, 0x74#8, 0x69#8, 0x6e#8, 0x75#8, 0x65#8, 0x27#8, 0x20#8, 0x6f#8, 0x75#8, 0x74#8, 0x73#8, 0x69#8, 0x64#8, 0x65#8, 0x20#8, 0x6f#8, 0x66#8, 0x20#8, 0x61#8, 0x20#8, 0x6c#8, 0x6f#8, 0x6f#8, 0x70#8]

abbrev topRet : TopSite where
  head := 0x80004540
  fmt := 0x80019550#64
  fmtBytes := topRetFmtBytes
  jal := topJalRet

abbrev topBrk : TopSite where
  head := 0x80004564
  fmt := 0x80019588#64
  fmtBytes := topBrkFmtBytes
  jal := topJalBrk

theorem topRet_ok : topRet.OK where
  jalCert := topJalRet_cert
  jalTgt := rfl
  jalText := by decide
  fmtText := by decide +kernel
  fmtNul := by decide +kernel
  fmtParse := by decide +kernel

theorem topBrk_ok : topBrk.OK where
  jalCert := topJalBrk_cert
  jalTgt := rfl
  jalText := by decide
  fmtText := by decide +kernel
  fmtNul := by decide +kernel
  fmtParse := by decide +kernel

end VsaIris.Newlib.TopAbrupt

import VsaIris.Vsa.BinImg
import VsaIris.CallAbort
import VsaIris.Vsa.Console
import Vsa.Sim.Code.FixedImage
import Vsa.Sim.LayoutInstance
import VsaIris.Vsa.HeapShape
import VsaIris.Vsa.StdioErr

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Interp VsaIris.Stdio VsaIris.Inst

theorem stdioFoot_off_alloc (a : Nat) (h : stdioFoot a) : ¬ VsaHeap.allocGlobal a := by
  unfold stdioFoot InRange at h
  unfold VsaHeap.allocGlobal VsaHeap.InRange
  omega

def gpV : BitVec 64 := 0x8001b510#64

def calleeSaved : List Nat := [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
def tmpRegs : List Nat := [5, 6, 7, 28, 29, 30, 31]
def argRegs : List Nat := [10, 11, 12, 13, 14, 15, 16, 17]

section Frame

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def argsAt (vs : List (BitVec 64)) : IProp GF :=
  iprop(sepL (vs.zipIdx) (fun p => (10 + p.2) ↦ᵣ p.1) ∗ clobbered (argRegs.drop vs.length))

structure SpIn (s : BitVec 64) (need : Nat) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 + need ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  align : s.toNat % 16 = 0

def callFrame (s : BitVec 64) (need : Nat) (saved : List Nat) (cs : Nat → BitVec 64) :
    IProp GF :=
  iprop(sp ↦ᵣ s ∗ stackScratch s need ∗ sepL saved (fun r => r ↦ᵣ cs r) ∗
    clobbered tmpRegs ∗ gp ↦ᵣ□ gpV ∗ binImg)

def cstrBuf (dst n : Nat) : IProp GF :=
  iprop(∃ img, ownImg (InExt (dst, n)) img ∗ ⌜∃ k, k < n ∧ img (dst + k) = 0⌝)

def readable (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) : IProp GF :=
  iprop(roImg Sro rd ∗ ownImg Sown rd)

end Frame

inductive Conv where
  | str
  | int
  deriving DecidableEq

def parseFmt : List (BitVec 8) → Option (List Conv)
  | [] => some []
  | b :: rest =>
    if b = 0x25#8 then
      match rest with
      | c :: r =>
        if c = 0x73#8 then (Conv.str :: ·) <$> parseFmt r
        else if c = 0x64#8 then (Conv.int :: ·) <$> parseFmt r
        else none
      | [] => none
    else parseFmt rest

def ReadAddr (a : Nat) : Prop :=
  0x80000000 ≤ a ∧ a + 8 ≤ 0x88000000 ∧ (a + 8 ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ a)

theorem readAddr_rodata {a : Nat} (h : rodataDom a) : ReadAddr a := by
  unfold rodataDom at h; unfold ReadAddr; omega

structure CStrCov (R : Nat → Prop) (rd : Nat → BitVec 8) (p : Nat) (bs : List (BitVec 8)) :
    Prop where
  bytes : ∀ i (h : i < bs.length), R (p + i) ∧ rd (p + i) = bs[i] ∧ bs[i] ≠ 0
  nul : R (p + bs.length) ∧ rd (p + bs.length) = 0
  win : ∀ i, i ≤ bs.length → ReadAddr (p + i)

structure FmtArgsAt (R : Nat → Prop) (rd : Nat → BitVec 8) (fmt : BitVec 64)
    (args : List (BitVec 64)) (bytes : List (BitVec 8)) (convs : List Conv) : Prop where
  fmt_str : CStrCov R rd fmt.toNat bytes
  parse : parseFmt bytes = some convs
  arity : convs.length ≤ args.length
  strs : ∀ i (h : i < convs.length), convs[i] = .str →
    ∃ t, CStrCov R rd (args[i]'(Nat.lt_of_lt_of_le h arity)).toNat t

theorem cstrCov_of_nul {R : Nat → Prop} {rd : Nat → BitVec 8} {p : Nat} :
    ∀ {n : Nat}, (∀ i, i < n → R (p + i)) → (∀ i, i < n → ReadAddr (p + i)) →
      (∃ k, k < n ∧ rd (p + k) = 0) → ∃ t, CStrCov R rd p t
  | 0, _, _, ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)
  | n + 1, hR, hW, h => by
    by_cases h' : ∃ k, k < n ∧ rd (p + k) = 0
    · exact cstrCov_of_nul (fun i hi => hR i (by omega)) (fun i hi => hW i (by omega)) h'
    · obtain ⟨k, hk, h0⟩ := h
      have hkn : k = n := by
        apply Classical.byContradiction; intro hne; exact h' ⟨k, by omega, h0⟩
      subst hkn
      refine ⟨(List.range k).map (fun i => rd (p + i)), ⟨fun i hi => ?_, ?_, fun i hi => ?_⟩⟩
      · have hi' : i < k := by simpa using hi
        refine ⟨hR i (by omega), by simp, ?_⟩
        simpa using fun hz => h' ⟨i, hi', hz⟩
      · simp only [List.length_map, List.length_range]
        exact ⟨hR k (by omega), h0⟩
      · simp only [List.length_map, List.length_range] at hi
        exact hW i (by omega)

theorem cstrCov_rodata {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {p : Nat} {bs : List (BitVec 8)}
    (hb : ∀ i (h : i < bs.length), rodataDom (p + i) ∧ rodataByte (p + i) = bs[i] ∧ bs[i] ≠ 0)
    (hn : rodataDom (p + bs.length) ∧ rodataByte (p + bs.length) = 0) : CStrCov R rd p bs where
  bytes i h := by
    obtain ⟨hd, hbv, hnz⟩ := hb i h
    obtain ⟨hR, hrd⟩ := hro _ hd
    exact ⟨hR, hrd.trans hbv, hnz⟩
  nul := by
    obtain ⟨hR, hrd⟩ := hro _ hn.1
    exact ⟨hR, hrd.trans hn.2⟩
  win i hi := by
    rcases Nat.lt_or_ge i bs.length with h | h
    · exact readAddr_rodata (hb i h).1
    · rw [show i = bs.length by omega]; exact readAddr_rodata hn.1

def FmtArgsOK (R : Nat → Prop) (rd : Nat → BitVec 8) (fmt : BitVec 64)
    (args : List (BitVec 64)) : Prop :=
  ∃ bytes convs, FmtArgsAt R rd fmt args bytes convs

def snprintfEntry : BitVec 64 := 0x80005c44#64
def fprintfEntry : BitVec 64 := 0x800061c0#64
def fwriteEntry : BitVec 64 := 0x80005260#64

def exitHandlersPC : BitVec 64 := 0x80004778#64
def exitHandlersEnd : BitVec 64 := 0x80004788#64

def stderrFile : BitVec 64 := 0x8001bbd8#64

def snprintfNeed : Nat := 1024
def fprintfNeed : Nat := 4096
def fwriteNeed : Nat := 768
def exitHandlersNeed : Nat := 256

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def snprintfSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s dst n fmt : BitVec 64) (args : List (BitVec 64)) (cs : Nat → BitVec 64)
    (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) : IProp GF :=
  fnSpecW Wp snprintfEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt ([dst, n, fmt] ++ args) ∗ blockOwn dst.toNat n.toNat ∗
      readable Sro Sown rd ∗ stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ cstrBuf dst.toNat n.toNat ∗ readable Sro Sown rd ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))

def errLineFmt : BitVec 64 := 0x800195e0#64

def fprintfSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live)) (s p : BitVec 64)
    (n : Nat) (bv : Nat → BitVec 8) (cs : Nat → BitVec 64) (o : String) : IProp GF :=
  fnSpecW Wp fprintfEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt [stderrFile, errLineFmt, p] ∗
      ownImg (InExt (p.toNat, n)) bv ∗ stdioOwn ∗ errnoOwn ∗ consoleOwn o ∗
      callFrame s fprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ ownImg (InExt (p.toNat, n)) bv ∗ stdioAt StdioErrOK ∗
      errnoOwn ∗ (∃ o', consoleOwn (o ++ o')) ∗ callFrame s fprintfNeed calleeSaved cs))

def fwriteSpec (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s ptr n : BitVec 64) (cs : Nat → BitVec 64)
    (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) (o : String) : IProp GF :=
  fnSpecW Wp fwriteEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt [ptr, 1#64, n, stderrFile] ∗ readable Sro Sown rd ∗
      stdioOwn ∗ errnoOwn ∗ consoleOwn o ∗ callFrame s fwriteNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ readable Sro Sown rd ∗ stdioAt StdioErrOK ∗ errnoOwn ∗
      (∃ o', consoleOwn (o ++ o')) ∗ callFrame s fwriteNeed calleeSaved cs))

def exitHandlersSpec (Ierr : (Nat → BitVec 8) → Prop) (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s e r : BitVec 64) (cs : Nat → BitVec 64)
    (o : String) (Φ : Nat × String → IProp GF) (quiet : Bool) : IProp GF :=
  iprop(PC ↦ᵣ exitHandlersPC ∗ ra ↦ᵣ r ∗ (8 : Nat) ↦ᵣ e ∗ argsAt [e, 0#64] ∗
      stdioAt (fun img => StdioOK img ∨ (quiet = false ∧ Ierr img)) ∗ errnoOwn ∗ consoleOwn o ∗
      callFrame s exitHandlersNeed (calleeSaved.drop 1) cs ∗
      (PC ↦ᵣ exitHandlersEnd -∗ (∃ w, ra ↦ᵣ w) -∗ (8 : Nat) ↦ᵣ e -∗ clobbered argRegs -∗
        stdioAt (fun _ => True) -∗ errnoOwn -∗
        (∃ o', ⌜quiet = true → o' = ""⌝ ∗ consoleOwn (o ++ o')) -∗
        callFrame s exitHandlersNeed (calleeSaved.drop 1) cs -∗ Wp.W Φ)
    -∗ Wp.W Φ)

end Specs

structure NewlibCoreAt (Ierr : (Nat → BitVec 8) → Prop) : Prop where

theorem NewlibCoreAt.proved (Ierr : (Nat → BitVec 8) → Prop) : NewlibCoreAt Ierr := ⟨⟩

def SnprintfProved : Prop :=
  ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s dst n fmt : BitVec 64) (args : List (BitVec 64))
    (cs : Nat → BitVec 64) (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8),
    CodeLive live → args.length ≤ 5 → 0 < n.toNat → n.toNat < 2 ^ 31 →
    FmtArgsOK (fun a => Sro a ∨ Sown a) rd fmt args → SpIn s snprintfNeed →
    0x8001c168 ≤ s.toNat - snprintfNeed → 0x8001c168 ≤ dst.toNat →
    dst.toNat + n.toNat ≤ 0x100000000 →
    ⊢ snprintfSpec live Wp s dst n fmt args cs Sro Sown rd

def FprintfProved : Prop :=
  ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s p : BitVec 64) (n : Nat) (bv : Nat → BitVec 8)
    (cs : Nat → BitVec 64) (o : String),
    CodeLive live → (∃ k, k < n ∧ bv (p.toNat + k) = 0) → n < 2 ^ 30 →
    0x80000000 ≤ p.toNat → p.toNat + n + 8 ≤ 0x100000000 →
    (p.toNat + n + 8 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 8 ≤ p.toNat) →
    SpIn s fprintfNeed → 0x80100000 ≤ s.toNat - fprintfNeed →
    ⊢ fprintfSpec live Wp s p n bv cs o

structure NewlibHolesAt (Ierr : (Nat → BitVec 8) → Prop) : Prop extends NewlibCoreAt Ierr where

  snprintf : SnprintfProved

  fprintf : FprintfProved

  exitHandlers : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s e r : BitVec 64) (cs : Nat → BitVec 64)
    (o : String) (Φ : Nat × String → IProp GF) (quiet : Bool),
    CodeLive live → SpIn s exitHandlersNeed →
    ⊢ exitHandlersSpec Ierr live Wp s e r cs o Φ quiet

def NewlibCore : Prop := NewlibCoreAt StdioErrOK

def NewlibHoles : Prop := NewlibHolesAt StdioErrOK

abbrev stdioErr (img : Nat → BitVec 8) : Prop := StdioErrOK img

theorem NewlibHoles.at (h : NewlibHoles) : NewlibHolesAt stdioErr := h

end VsaIris.Newlib

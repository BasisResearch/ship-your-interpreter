import VsaIris.Vsa.SegRun
import Vsa.Sim.StrlenSegments
import Vsa.Sim.StrlenMagic
import Vsa.Sim.StrlenSpecU

namespace VsaIris.Inst.Strlen

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Vsa.Sim Vsa.MemRepr

#derive_case strlenX6d60LoadSeg chain
  [(0x80006d60#64, 0xffe74783#32)]

#derive_case strlenX6d68Seg chain
  [(0x80006d68#64, 0x00d50533#32),
   (0x80006d6c#64, 0xffe50513#32)]
    terminator ⟨0x80006d70#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strlenX6d88Seg chain
  [(0x80006d88#64, 0x40a70733#32),
   (0x80006d8c#64, 0xfff70513#32)]
    terminator ⟨0x80006d90#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

abbrev codeBase : Nat := 0x80006cf0

def strlenCodeA : List (BitVec 8) :=
  [0x93#8, 0x77#8, 0x75#8, 0x00#8, 0x13#8, 0x07#8, 0x05#8, 0x00#8, 0x63#8, 0x90#8, 0x07#8, 0x08#8,
   0xb7#8, 0x87#8, 0x7f#8, 0x7f#8, 0x93#8, 0x87#8, 0xf7#8, 0xf7#8, 0x93#8, 0x96#8, 0x07#8, 0x02#8,
   0xb3#8, 0x86#8, 0xf6#8, 0x00#8, 0x93#8, 0x05#8, 0xf0#8, 0xff#8, 0x03#8, 0x36#8, 0x07#8, 0x00#8,
   0x13#8, 0x07#8, 0x87#8, 0x00#8, 0xb3#8, 0x77#8, 0xd6#8, 0x00#8, 0xb3#8, 0x87#8, 0xd7#8, 0x00#8,
   0xb3#8, 0xe7#8, 0xc7#8, 0x00#8, 0xb3#8]

def strlenCodeB : List (BitVec 8) :=
  [0xe7#8, 0xd7#8, 0x00#8, 0xe3#8, 0x84#8, 0xb7#8, 0xfe#8, 0x83#8, 0x47#8, 0x87#8, 0xff#8, 0xb3#8,
   0x06#8, 0xa7#8, 0x40#8, 0x63#8, 0x84#8, 0x07#8, 0x06#8, 0x83#8, 0x47#8, 0x97#8, 0xff#8, 0x63#8,
   0x8c#8, 0x07#8, 0x04#8, 0x83#8, 0x47#8, 0xa7#8, 0xff#8, 0x63#8, 0x84#8, 0x07#8, 0x06#8, 0x83#8,
   0x47#8, 0xb7#8, 0xff#8, 0x63#8, 0x8c#8, 0x07#8, 0x04#8, 0x83#8, 0x47#8, 0xc7#8, 0xff#8, 0x63#8,
   0x80#8, 0x07#8, 0x06#8, 0x83#8, 0x47#8]

def strlenCodeC : List (BitVec 8) :=
  [0xd7#8, 0xff#8, 0x63#8, 0x80#8, 0x07#8, 0x06#8, 0x83#8, 0x47#8, 0xe7#8, 0xff#8, 0x33#8, 0x35#8,
   0xf0#8, 0x00#8, 0x33#8, 0x05#8, 0xd5#8, 0x00#8, 0x13#8, 0x05#8, 0xe5#8, 0xff#8, 0x67#8, 0x80#8,
   0x00#8, 0x00#8, 0xe3#8, 0x84#8, 0x06#8, 0xf8#8, 0x83#8, 0x47#8, 0x07#8, 0x00#8, 0x13#8, 0x07#8,
   0x17#8, 0x00#8, 0x93#8, 0x76#8, 0x77#8, 0x00#8, 0xe3#8, 0x98#8, 0x07#8, 0xfe#8, 0x33#8, 0x07#8,
   0xa7#8, 0x40#8, 0x13#8, 0x05#8, 0xf7#8]

def strlenCodeD : List (BitVec 8) :=
  [0xff#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x85#8, 0x96#8, 0xff#8, 0x67#8, 0x80#8, 0x00#8,
   0x00#8, 0x13#8, 0x85#8, 0x86#8, 0xff#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x85#8, 0xb6#8,
   0xff#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x85#8, 0xa6#8, 0xff#8, 0x67#8, 0x80#8, 0x00#8,
   0x00#8, 0x13#8, 0x85#8, 0xc6#8, 0xff#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x85#8, 0xd6#8,
   0xff#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8]

def strlenCode : List (BitVec 8) :=
  strlenCodeA ++ strlenCodeB ++ strlenCodeC ++ strlenCodeD

def codeText (i : Nat) (code : List (BitVec 8)) : List (Nat × BitVec 8) :=
  code.zipIdx.map (fun q => (i + q.2, q.1))

def memFoot (t : List (Nat × BitVec 8)) : List (Nat × DFrac × BitVec 8) :=
  t.map (fun q => (q.1, DFrac.discard, q.2))

theorem instrAt_text {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    (i : Nat) (code : List (BitVec 8)) :
    instrAt (GF := GF) i code = sepL (codeText i code) (fun q => q.1 ↦ₘ□ q.2) := by
  unfold instrAt codeText
  rw [sepL_map]

theorem strlenLoaded_of_code {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ q ∈ memFoot (codeText codeBase strlenCode), m[q.1]? = some q.2.2) :
    Code.StrlenLoaded m := by
  have h' : ∀ a b, (a, b) ∈ codeText codeBase strlenCode → m[a]? = some b := by
    intro a b hab
    exact h (a, DFrac.discard, b) (List.mem_map_of_mem (f := fun q => (q.1, DFrac.discard, q.2)) hab)
  exact Vsa.Sim.TextIn.of_list (fun p hp => h' p.1 p.2 hp) (by decide +kernel)

def strText (p len : Nat) (bv : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  (List.range (len + 1)).map (fun k => (p + k, bv (p + k)))

def regionText (p len : Nat) (bv : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  (List.range (len + 8)).map (fun k => (p + k, bv (p + k)))

def slackSet (p len : Nat) (a : Nat) : Prop := p + len + 1 ≤ a ∧ a < p + len + 8

def strlenText (p len : Nat) (bv : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  codeText codeBase strlenCode ++ strText p len bv

def strlenMR (p len : Nat) (bv : Nat → BitVec 8) : List (Nat × DFrac × BitVec 8) :=
  memFoot (codeText codeBase strlenCode ++ regionText p len bv)

theorem mem_memFoot {t : List (Nat × BitVec 8)} {q : Nat × DFrac × BitVec 8}
    (h : q ∈ memFoot t) : (q.1, q.2.2) ∈ t := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  exact hx

theorem memFoot_mem {t : List (Nat × BitVec 8)} {x : Nat × BitVec 8} (h : x ∈ t) :
    (x.1, DFrac.discard, x.2) ∈ memFoot t :=
  List.mem_map_of_mem (f := fun q : Nat × BitVec 8 => (q.1, DFrac.discard, q.2)) h

theorem mem_regionText (p len k : Nat) (bv : Nat → BitVec 8) (hk : k < len + 8) :
    (p + k, bv (p + k)) ∈ regionText p len bv :=
  List.mem_map_of_mem (l := List.range (len + 8)) (f := fun k => (p + k, bv (p + k)))
    (List.mem_range.mpr hk)

theorem mem_strText (p len k : Nat) (bv : Nat → BitVec 8) (hk : k ≤ len) :
    (p + k, bv (p + k)) ∈ strText p len bv :=
  List.mem_map_of_mem (l := List.range (len + 1)) (f := fun k => (p + k, bv (p + k)))
    (List.mem_range.mpr (by omega))

structure Reads (p len : Nat) (bv : Nat → BitVec 8) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  loaded : Code.StrlenLoaded m
  bytes : ∀ k, k < len + 8 → m[p + k]? = some (bv (p + k))

theorem reads_of_foot {live : Nat → Prop} {c : Config} {p len : Nat} {bv : Nat → BitVec 8}
    (hok : VsaOk live c) (hlive : ∀ q ∈ strlenMR p len bv, live q.1)
    (hfoot : ∀ q ∈ strlenMR p len bv, (vsaModel live).mem c q.1 = q.2.2) :
    Reads p len bv c.σ.mem := by
  have hpres := code_present hok (strlenMR p len bv) hfoot hlive
  have hcode : ∀ q ∈ memFoot (codeText codeBase strlenCode), c.σ.mem[q.1]? = some q.2.2 := by
    intro q hq
    refine hpres q ?_
    unfold strlenMR memFoot
    rw [List.map_append]
    exact List.mem_append_left _ hq
  refine ⟨strlenLoaded_of_code hcode, fun k hk => ?_⟩
  refine hpres (p + k, DFrac.discard, bv (p + k)) ?_
  unfold strlenMR
  refine memFoot_mem (t := codeText codeBase strlenCode ++ regionText p len bv)
    (x := (p + k, bv (p + k))) (List.mem_append_right _ ?_)
  exact mem_regionText p len k bv hk

theorem strlenMR_split {p len : Nat} {bv mv : Nat → BitVec 8}
    (hslack : ∀ a, slackSet p len a → mv a = bv a) :
    ∀ q ∈ strlenMR p len bv,
      (q.1, q.2.2) ∈ strlenText p len bv ∨ (slackSet p len q.1 ∧ mv q.1 = q.2.2) := by
  intro q hq
  rcases List.mem_append.mp (mem_memFoot hq) with h | h
  · exact .inl (List.mem_append_left _ h)
  · obtain ⟨k, hk, he⟩ := List.mem_map.mp h
    have hk' := List.mem_range.mp hk
    have h1 : p + k = q.1 := congrArg Prod.fst he
    have h2 : bv (p + k) = q.2.2 := congrArg Prod.snd he
    by_cases hle : k ≤ len
    · refine .inl (List.mem_append_right _ ?_)
      rw [← h1, ← h2]
      exact mem_strText p len k bv hle
    · have hs : slackSet p len q.1 := by rw [← h1]; exact ⟨by omega, by omega⟩
      refine .inr ⟨hs, ?_⟩
      rw [← h1, ← h2]
      exact hslack _ (by rw [h1]; exact hs)

structure StrBytes (p len : Nat) (bv : Nat → BitVec 8) : Prop where
  nonzero : ∀ k, k < len → bv (p + k) ≠ 0
  nul : bv (p + len) = 0

def strlenRegs : List Nat := [1, 10, 11, 12, 13, 14, 15]

def strlenRs : List Nat := VsaIris.PC :: strlenRegs

def strlenL (rv : Nat → BitVec 64) : GRegs :=
  [(1, rv 1), (10, rv 10), (11, rv 11), (12, rv 12), (13, rv 13), (14, rv 14), (15, rv 15)]

theorem strlenL_eq (rv : Nat → BitVec 64) : strlenL rv = leafL strlenRegs rv := rfl

def strlenQ (r : BitVec 64) (p len : Nat) (bv : Nat → BitVec 8)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  rv VsaIris.PC = r ∧ rv 1 = r ∧ rv 10 = BitVec.ofNat 64 len ∧
    ∀ a, slackSet p len a → mv a = bv a

abbrev SRun (live : Nat → Prop) (p len : Nat) (bv : Nat → BitVec 8) (r : BitVec 64)
    (n : Nat) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  LocalRun (vsaModel live) [] (strlenText p len bv) strlenRs (slackSet p len)
    (strlenQ r p len bv) n rv mv

theorem strlenStep {live : Nat → Prop} {p len : Nat} {bv : Nat → BitVec 8} {r : BitVec 64}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (m : Nat)
    (bs : List BBlock) (lds : List (List (BitVec 8))) (pc0 : BitVec 64) (n : Nat)
    (hlen : evalBlocksFuel bs = n + 1)
    (hwf : ChainOK pc0 strlenRegs bs)
    (hwr : ∀ k ∈ wrChain bs, k ∈ strlenRegs)
    (hsilent : (segOut bs (strlenL rv) lds).log = [])
    (hlive : ∀ q ∈ strlenMR p len bv, live q.1)
    (hslack : ∀ a, slackSet p len a → mv a = bv a)
    (hpc : rv VsaIris.PC = pc0)
    (hfacts : ∀ σ : Vsa.Machine.MState, Reads p len bv σ.mem →
      ChainFacts σ.mem σ.mem (strlenL rv) lds bs)
    (hnext : ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init (strlenL rv) lds) bs →
      (∀ k ∈ strlenRegs, rv' k = finReg bs (strlenL rv) lds k) →
      (∀ a, slackSet p len a → mv' a = bv a) →
      SRun live p len bv r m rv' mv') :
    SRun live p len bv r (m + 1) rv mv :=
  leafStep strlenRegs m bs lds pc0 (strlenMR p len bv) [] n hlen (by decide) hwf hwr
    (fun a _ => by rw [← strlenL_eq, hsilent]; trivial)
    (fun c hok hfoot => hfacts c.σ (reads_of_foot hok hlive hfoot.2.1))
    (strlenMR_split hslack) (fun q hq => nomatch hq) hpc
    (fun rv' mv' h1 h2 _ h4 =>
      hnext rv' mv' h1 h2 (fun a ha => (h4 a ha (fun q hq => nomatch hq)).trans (hslack a ha)))

theorem strlenAluStep {live : Nat → Prop} {p len : Nat} {bv : Nat → BitVec 8} {r : BitVec 64}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (m : Nat) (i : Nat) (rd rsrc : Nat)
    (val : BitVec 64)
    (hrd : rd ∈ strlenRegs) (hrs : rsrc ∈ strlenRegs)
    (hslack : ∀ a, slackSet p len a → mv a = bv a)
    (hpc : rv VsaIris.PC = BitVec.ofNat 64 i)
    (hstep : AluStep live i [(rsrc, DFrac.own 1, rv rsrc)] (strlenMR p len bv) rd val)
    (hnext : ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = BitVec.ofNat 64 (i + 4) → rv' rd = val →
      (∀ j ∈ strlenRegs, j ≠ rd → rv' j = rv j) →
      (∀ a, slackSet p len a → mv' a = bv a) →
      SRun live p len bv r m rv' mv') :
    SRun live p len bv r (m + 1) rv mv := by
  have hregLt : ∀ j ∈ strlenRegs, j ≠ VsaIris.PC := by
    intro j hj
    simp only [strlenRegs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine Or.inr ⟨0, segFrom_of_runFact (runFact_of_aluStep (old := rv rd) hstep)
    (fun q hq => ?_) (strlenMR_split hslack) (fun q hq => ?_) (fun q hq => nomatch hq) ?_⟩
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact .inr ⟨by unfold strlenRs; exact .tail _ hrs, rfl⟩
    · cases hq
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact .inl ⟨by unfold strlenRs; exact List.mem_cons_self, hpc⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact .inl ⟨by unfold strlenRs; exact .tail _ hrd, rfl⟩
      · cases hq
  · intro rv' mv' hnew hframe _ hmem
    refine hnext rv' mv' (hnew _ List.mem_cons_self)
      (hnew _ (.tail _ List.mem_cons_self)) (fun j hj hjrd => ?_)
      (fun a ha => (hmem a ha (fun q hq => nomatch hq)).trans (hslack a ha))
    refine hframe j (by unfold strlenRs; exact .tail _ hj) (fun q hq => ?_)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact fun e => hregLt j hj e.symm
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact fun e => hjrd e.symm
      · cases hq

end VsaIris.Inst.Strlen

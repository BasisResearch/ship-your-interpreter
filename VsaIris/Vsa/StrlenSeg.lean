import VsaIris.Vsa.SegRun
import Vsa.Sim.StrlenSegments
import Vsa.Sim.StrlenMagic
import Vsa.Sim.StrlenSpecU

/-!
# `strlen`: code, read region, and the uniform segment step

INTERP_DESIGN.md §9, package H3. `strlen` (`0x80006cf0 … 0x80006dc4`) is a leaf:
no stack frame, no calls, and no store. So the WHOLE function is ONE
`LocalRun` (`VsaIris/LocalRun.lean`), and the Iris layer is a single
`wp_localRunW` application (`Strlen.lean`).

This file fixes the pieces every step of that run shares:

* `strlenCode` / `strlenLoaded_of_code`: the 212 code bytes as persistent text,
  and VSA's fetch predicate `Code.StrlenLoaded` read off them;
* the read region `[p, p+len+8)`: the string and its NUL (`strText`,
  persistent) and the ≤ 7 bytes the word load over-reads past the NUL
  (`slackSet`, owned and returned unchanged) — `StrlenReadRegions` is exactly
  this geometry, so VSA's own load-bound and detection lemmas apply verbatim;
* `Reads`: the two facts a step's `ChainFacts` needs, derived once from the
  footprint (`reads_of_foot`);
* `strlenL` / `strlenStep`: ONE pin list (all seven GPRs `strlen` touches) and
  ONE step combinator, so a segment contributes a `ChainFacts` and nothing
  else.

`gen_fn.py --fn strlen --entry 0x80006cf0` emits a segment for every block.
`Vsa/Sim/StrlenSegments.lean` retains all but two. One of those,
`0x80006d88` (the byte-peel exit, `sub a4,a4,a0; addi a0,a4,-1; ret`), is
declared here: it is ordinary and its `ChainFacts` discharge.

The other, `0x80006d60` (the `snez` tail), is NOT declared: `snez rd,rs` is
`sltu rd,x0,rs`, and `MKind` (`Vsa/Sim/BlockMem.lean:549`) has `slt` but no
`sltu`. `#derive_case` still accepts the word — it decodes it to the nearest
kind — but the block's `DecodeFactM` then cannot be closed, because
`DecodeTable.decode_00f03533` concludes `rop.SLTU` while `astOfM` of the
reflected line does not. That is the model's safety net working, and it is
why `Vsa/Sim/StrlenLastRun.lean` proves that one instruction observationally.
The Iris route reuses the same generated site (`StrlenSites.site_80006d64`)
through `Inst.runFact_of_aluStep` (`SegRun.lean`). Adding `sltu` to `MKind`
would retire both.
-/

namespace VsaIris.Inst.Strlen

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Vsa.Sim Vsa.MemRepr

/-! ## The segments `Vsa/Sim/StrlenSegments.lean` does not retain -/

/- `0x80006d60`: the last byte's load, on its own (the `snez` that follows is
not in the block model; see the module doc). -/
#derive_case strlenX6d60LoadSeg chain
  [(0x80006d60#64, 0xffe74783#32)]  -- lbu a5,-2(a4)

/- `0x80006d68 … 0x80006d70`: the arithmetic return after the `snez`
(`add a0,a0,a3; addi a0,a0,-2; ret`). -/
#derive_case strlenX6d68Seg chain
  [(0x80006d68#64, 0x00d50533#32),  -- add a0,a0,a3
   (0x80006d6c#64, 0xffe50513#32)]  -- addi a0,a0,-2
    terminator ⟨0x80006d70#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

/- `0x80006d88 … 0x80006d90`: the byte-peel exit (`sub a4,a4,a0;
addi a0,a4,-1; ret`). -/
#derive_case strlenX6d88Seg chain
  [(0x80006d88#64, 0x40a70733#32),  -- sub a4,a4,a0
   (0x80006d8c#64, 0xfff70513#32)]  -- addi a0,a4,-1
    terminator ⟨0x80006d90#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

/-! ## Code -/

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

/-- The 212 code bytes of `strlen`, in four chunks so that list length and
membership stay inside the default elaboration recursion depth. -/
def strlenCode : List (BitVec 8) :=
  strlenCodeA ++ strlenCodeB ++ strlenCodeC ++ strlenCodeD

/-- Persistent bytes as a `LocalRun` text list. -/
def codeText (i : Nat) (code : List (BitVec 8)) : List (Nat × BitVec 8) :=
  code.zipIdx.map (fun q => (i + q.2, q.1))

/-- The read footprint of a list of known bytes. -/
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
  unfold Code.StrlenLoaded Code.strlenChunk0 Code.strlenChunk1 Code.strlenChunk2 Code.strlenChunk3
  repeat' apply And.intro
  all_goals (apply h'; decide)

/-! ## The read region

`strlen` reads `[p, p+len]` — the string and its NUL — and, because the word
loop loads whole aligned 8-byte words, at most seven bytes past the NUL. That
is exactly VSA's own `StrlenReadRegions` geometry. The string bytes are
persistent text; the seven slack bytes are owned (they belong to the caller's
heap block) and are handed back unchanged. -/

/-- The persistent string bytes: `[p, p+len]`. -/
def strText (p len : Nat) (bv : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  (List.range (len + 1)).map (fun k => (p + k, bv (p + k)))

/-- Every byte the run may read: `[p, p+len+8)`. -/
def regionText (p len : Nat) (bv : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  (List.range (len + 8)).map (fun k => (p + k, bv (p + k)))

/-- The owned slack: the bytes past the NUL inside the last word. -/
def slackSet (p len : Nat) (a : Nat) : Prop := p + len + 1 ≤ a ∧ a < p + len + 8

/-- The persistent cells of a `strlen` run: its code and the string. -/
def strlenText (p len : Nat) (bv : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  codeText codeBase strlenCode ++ strText p len bv

/-- The read footprint of every `strlen` step. -/
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

/-- **What a step reads.** VSA's fetch predicate and the region's bytes,
present with their values. -/
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

/-- Liveness of the read footprint, from the two intervals. -/
theorem strlenCode_length : strlenCode.length = 212 := by
  simp only [strlenCode, List.length_append]
  rfl

theorem strlenMR_live {live : Nat → Prop} {p len : Nat} {bv : Nat → BitVec 8}
    (hcode : ∀ a, codeBase ≤ a → a < codeBase + 212 → live a)
    (hstr : ∀ a, p ≤ a → a < p + len + 8 → live a) :
    ∀ q ∈ strlenMR p len bv, live q.1 := by
  intro q hq
  rcases List.mem_append.mp (mem_memFoot hq) with h | h
  · obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    have hlt : x.2 < 212 := by
      have := List.snd_lt_of_mem_zipIdx hx
      rw [strlenCode_length] at this
      omega
    have h1 : codeBase + x.2 = q.1 := congrArg Prod.fst he
    exact hcode _ (by omega) (by omega)
  · obtain ⟨k, hk, he⟩ := List.mem_map.mp h
    have hk' := List.mem_range.mp hk
    have h1 : p + k = q.1 := congrArg Prod.fst he
    exact hstr _ (by omega) (by omega)

/-- Where each read byte lives: persistent text, or an owned slack byte. -/
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

/-! ## The string as a `CStr` -/

/-- The characters of the region. -/
def charsOf (p len : Nat) (bv : Nat → BitVec 8) : List Char :=
  (List.range len).map (fun k => Char.ofNat (bv (p + k)).toNat)

theorem charsOf_length (p len : Nat) (bv : Nat → BitVec 8) :
    (charsOf p len bv).length = len := by simp [charsOf]

/-- A NUL-terminated ASCII string in the region. -/
structure StrBytes (p len : Nat) (bv : Nat → BitVec 8) : Prop where
  nonzero : ∀ k, k < len → bv (p + k) ≠ 0
  ascii : ∀ k, k < len → (bv (p + k)).toNat < 128
  nul : bv (p + len) = 0

theorem charsOf_succ (p len : Nat) (bv : Nat → BitVec 8) :
    charsOf p (len + 1) bv = Char.ofNat (bv p).toNat :: charsOf (p + 1) len bv := by
  unfold charsOf
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [show p + (k + 1) = p + 1 + k from by omega]

theorem cstr_of_bytes {m : Std.ExtHashMap Nat (BitVec 8)} : ∀ (len p : Nat) (bv : Nat → BitVec 8),
    StrBytes p len bv → (∀ k, k ≤ len → m[p + k]? = some (bv (p + k))) →
    CStr m p (charsOf p len bv)
  | 0, p, bv, hb, hm => by
    refine .nil ?_
    have h0 := hm 0 (by omega)
    have hn := hb.nul
    rw [Nat.add_zero] at h0 hn
    rw [h0, hn]
  | len + 1, p, bv, hb, hm => by
    rw [charsOf_succ]
    refine .cons (b := bv p) ?_ ?_ ?_ ?_
    · have := hm 0 (by omega); rwa [Nat.add_zero] at this
    · have := hb.nonzero 0 (by omega); rwa [Nat.add_zero] at this
    · have := hb.ascii 0 (by omega); rwa [Nat.add_zero] at this
    · refine cstr_of_bytes len (p + 1) bv
        ⟨fun k hk => by rw [show p + 1 + k = p + (k + 1) from by omega]; exact hb.nonzero _ (by omega),
         fun k hk => by rw [show p + 1 + k = p + (k + 1) from by omega]; exact hb.ascii _ (by omega),
         by rw [show p + 1 + len = p + (len + 1) from by omega]; exact hb.nul⟩
        fun k hk => by
          rw [show p + 1 + k = p + (k + 1) from by omega]; exact hm _ (by omega)

theorem cstr_of_reads {m : Std.ExtHashMap Nat (BitVec 8)} {p len : Nat} {bv : Nat → BitVec 8}
    (hb : StrBytes p len bv) (hr : Reads p len bv m) : CStr m p (charsOf p len bv) :=
  cstr_of_bytes len p bv hb fun k hk => hr.bytes k (by omega)


/-! ## One pin list, one step

`strlen` touches seven GPRs and nothing else, so every segment of the run is
pinned at the SAME list. That makes `hwf`/`hkeys`/`hwr` one `decide` each and
lets `strlenStep` present a segment as: its `ChainFacts`, and the successor's
seven register values. -/

/-- The GPRs `strlen` reads or writes: `ra a0 a1 a2 a3 a4 a5`. -/
def strlenRegs : List Nat := [1, 10, 11, 12, 13, 14, 15]

/-- The run's owned registers: the PC and those seven. -/
def strlenRs : List Nat := VsaIris.PC :: strlenRegs

/-- The uniform pin list, read off the run's register valuation. -/
def strlenL (rv : Nat → BitVec 64) : GRegs :=
  [(1, rv 1), (10, rv 10), (11, rv 11), (12, rv 12), (13, rv 13), (14, rv 14), (15, rv 15)]

theorem keysG_strlenL (rv : Nat → BitVec 64) : keysG (strlenL rv) = strlenRegs := rfl

/-- **The run's end condition**: parked at the return address with the length
in `a0`, `ra` restored, and the owned slack bytes unchanged. -/
def strlenQ (r : BitVec 64) (p len : Nat) (bv : Nat → BitVec 8)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  rv VsaIris.PC = r ∧ rv 1 = r ∧ rv 10 = BitVec.ofNat 64 len ∧
    ∀ a, slackSet p len a → mv a = bv a

/-- The whole of `strlen` as one bounded owned-footprint run. -/
abbrev SRun (live : Nat → Prop) (p len : Nat) (bv : Nat → BitVec 8) (r : BitVec 64)
    (n : Nat) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  LocalRun (vsaModel live) [] (strlenText p len bv) strlenRs (slackSet p len)
    (strlenQ r p len bv) n rv mv

/-- **One reflected `strlen` segment.** -/
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
    (hfacts : ∀ m0 : Std.ExtHashMap Nat (BitVec 8), Reads p len bv m0 →
      ChainFacts m0 m0 (strlenL rv) lds bs)
    (hnext : ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init (strlenL rv) lds) bs →
      (∀ k ∈ strlenRegs, rv' k = finReg bs (strlenL rv) lds k) →
      (∀ a, slackSet p len a → mv' a = bv a) →
      SRun live p len bv r m rv' mv') :
    SRun live p len bv r (m + 1) rv mv := by
  refine Or.inr ⟨n, segFrom_of_seg bs (strlenL rv) lds pc0 (strlenMR p len bv) n hlen
    (by rw [keysG_strlenL]; exact hwf) (by rw [keysG_strlenL]; decide)
    (by rw [keysG_strlenL]; exact hwr) hsilent
    (fun c hok hfoot => hfacts c.σ.mem (reads_of_foot hok hlive hfoot.2.1))
    (strlenMR_split hslack) (by unfold strlenRs; exact List.mem_cons_self) hpc ?_ ?_⟩
  · intro q hq
    simp only [strlenL, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp [strlenRs, strlenRegs], rfl⟩
  · intro rv' mv' hpc' hfin _ hmem
    refine hnext rv' mv' hpc' (fun k hk => ?_) (fun a ha => (hmem a ha).trans (hslack a ha))
    simp only [strlenRegs, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfin (1, rv 1) (by simp [strlenL])
    · exact hfin (10, rv 10) (by simp [strlenL])
    · exact hfin (11, rv 11) (by simp [strlenL])
    · exact hfin (12, rv 12) (by simp [strlenL])
    · exact hfin (13, rv 13) (by simp [strlenL])
    · exact hfin (14, rv 14) (by simp [strlenL])
    · exact hfin (15, rv 15) (by simp [strlenL])

/-- **One observational ALU step of the run** (the `snez` at `0x80006d64`,
which `MKind` does not cover). The step reads one GPR and writes one. -/
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
    · exact ⟨by unfold strlenRs; exact List.mem_cons_self, hpc⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨by unfold strlenRs; exact .tail _ hrd, rfl⟩
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

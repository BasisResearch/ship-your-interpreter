import VsaIris.Vsa.SymData
import VsaIris.Vsa.SymObs
import VsaIris.Vsa.StrlenSeg
import VsaIris.Vsa.BinImg
import Vsa.Sim.MemcpySites4
import Vsa.Sim.MemcpySpec4
import Vsa.Sim.MemcpyCopyWordMemory

/-!
# `memcpy`'s symbolic runs

`memcpy` (`0x80006bc8 … 0x80006cf0`) is a leaf that reads a READ-ONLY source
and writes an owned destination. Its callers own neither `gp` nor newlib's
data, so the allocator's `SWP` (read-only register `gp`, code `allocText`)
does not apply. `MW` is `SWP` with no read-only register, the read-only list
split into memcpy's live code `mText` and the source bytes `srcText` (total
reads, no liveness: `SymData.swp_segLD`'s split), and the owned registers
`mRegs`.

* `mw_step`: one reflected segment (`swp_stepD` without `gp`). The step table
  `MemcpySteps.lean` instantiates it per instruction, over the allocator
  table's segments `ax_<pc>` (`AllocSteps/Part09.lean`).
* `mw_alu`: the `sltiu` at `0x80006bd8` (outside `MKind`), VSA's observed
  site `site_80006bd8` through `aluStep_of_obs`.
* `mw_done`, `mw_congr`: the end of a run; restating the register file.
-/

namespace VsaIris.Memcpy

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast VsaIris.Sym
open Vsa.Machine (Config)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Code -/

abbrev memcpyBase : Nat := 0x80006bc8

def memcpyCodeA : List (BitVec 8) :=
  [0xb3#8, 0xc7#8, 0xa5#8, 0x00#8, 0x93#8, 0xf7#8, 0x77#8, 0x00#8, 0xb3#8, 0x08#8, 0xc5#8, 0x00#8,
   0x63#8, 0x96#8, 0x07#8, 0x06#8, 0x13#8, 0x36#8, 0x86#8, 0x00#8, 0x63#8, 0x12#8, 0x06#8, 0x06#8,
   0x93#8, 0x77#8, 0x75#8, 0x00#8, 0x13#8, 0x07#8, 0x05#8, 0x00#8, 0x63#8, 0x9a#8, 0x07#8, 0x0c#8,
   0x13#8, 0xf6#8, 0x88#8, 0xff#8, 0xb3#8, 0x06#8, 0xe6#8, 0x40#8, 0x93#8, 0x07#8, 0x00#8, 0x04#8,
   0x63#8, 0xc4#8, 0xd7#8, 0x06#8, 0x93#8, 0x86#8, 0x05#8, 0x00#8, 0x93#8, 0x07#8, 0x07#8, 0x00#8,
   0x63#8, 0x7a#8, 0xc7#8, 0x02#8, 0x03#8, 0xb8#8, 0x06#8, 0x00#8, 0x93#8, 0x87#8, 0x87#8, 0x00#8,
   0x93#8, 0x86#8]

def memcpyCodeB : List (BitVec 8) :=
  [0x86#8, 0x00#8, 0x23#8, 0xbc#8, 0x07#8, 0xff#8, 0xe3#8, 0xe8#8, 0xc7#8, 0xfe#8, 0x13#8, 0x06#8,
   0xf6#8, 0xff#8, 0x33#8, 0x06#8, 0xe6#8, 0x40#8, 0x13#8, 0x76#8, 0x86#8, 0xff#8, 0x93#8, 0x85#8,
   0x85#8, 0x00#8, 0x13#8, 0x07#8, 0x87#8, 0x00#8, 0xb3#8, 0x85#8, 0xc5#8, 0x00#8, 0x33#8, 0x07#8,
   0xc7#8, 0x00#8, 0x63#8, 0x68#8, 0x17#8, 0x01#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x07#8,
   0x05#8, 0x00#8, 0xe3#8, 0x7c#8, 0x15#8, 0xff#8, 0x83#8, 0xc7#8, 0x05#8, 0x00#8, 0x13#8, 0x07#8,
   0x17#8, 0x00#8, 0x93#8, 0x85#8, 0x15#8, 0x00#8, 0xa3#8, 0x0f#8, 0xf7#8, 0xfe#8, 0xe3#8, 0x98#8,
   0xe8#8, 0xfe#8]

def memcpyCodeC : List (BitVec 8) :=
  [0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x83#8, 0xb6#8, 0x05#8, 0x00#8, 0x83#8, 0xb2#8, 0x85#8, 0x00#8,
   0x83#8, 0xbf#8, 0x05#8, 0x01#8, 0x03#8, 0xbf#8, 0x85#8, 0x01#8, 0x83#8, 0xbe#8, 0x05#8, 0x02#8,
   0x03#8, 0xbe#8, 0x85#8, 0x02#8, 0x03#8, 0xb3#8, 0x05#8, 0x03#8, 0x03#8, 0xb8#8, 0x85#8, 0x03#8,
   0x23#8, 0x30#8, 0xd7#8, 0x00#8, 0x83#8, 0xb6#8, 0x05#8, 0x04#8, 0x13#8, 0x07#8, 0x87#8, 0x04#8,
   0x23#8, 0x30#8, 0x57#8, 0xfc#8, 0x23#8, 0x3c#8, 0xd7#8, 0xfe#8, 0x23#8, 0x34#8, 0xf7#8, 0xfd#8,
   0xb3#8, 0x06#8, 0xe6#8, 0x40#8, 0x23#8, 0x38#8, 0xe7#8, 0xfd#8, 0x23#8, 0x3c#8, 0xd7#8, 0xfd#8,
   0x23#8, 0x30#8]

def memcpyCodeD : List (BitVec 8) :=
  [0xc7#8, 0xff#8, 0x23#8, 0x34#8, 0x67#8, 0xfe#8, 0x23#8, 0x38#8, 0x07#8, 0xff#8, 0x93#8, 0x85#8,
   0x85#8, 0x04#8, 0xe3#8, 0xc6#8, 0xd7#8, 0xfa#8, 0x6f#8, 0xf0#8, 0x5f#8, 0xf4#8, 0x83#8, 0xc6#8,
   0x05#8, 0x00#8, 0x13#8, 0x07#8, 0x17#8, 0x00#8, 0x93#8, 0x77#8, 0x77#8, 0x00#8, 0xa3#8, 0x0f#8,
   0xd7#8, 0xfe#8, 0x93#8, 0x85#8, 0x15#8, 0x00#8, 0xe3#8, 0x8e#8, 0x07#8, 0xf0#8, 0x83#8, 0xc6#8,
   0x05#8, 0x00#8, 0x13#8, 0x07#8, 0x17#8, 0x00#8, 0x93#8, 0x77#8, 0x77#8, 0x00#8, 0xa3#8, 0x0f#8,
   0xd7#8, 0xfe#8, 0x93#8, 0x85#8, 0x15#8, 0x00#8, 0xe3#8, 0x9a#8, 0x07#8, 0xfc#8, 0x6f#8, 0xf0#8,
   0x1f#8, 0xf0#8]

/-- The 296 code bytes of `memcpy`, in four chunks. -/
def memcpyCode : List (BitVec 8) := memcpyCodeA ++ memcpyCodeB ++ memcpyCodeC ++ memcpyCodeD

/-- `memcpy`'s code as read-only cells. -/
abbrev mText : List (Nat × BitVec 8) := Strlen.codeText memcpyBase memcpyCode

/-- VSA's fetch predicate, read off the code cells. -/
theorem memcpyLoaded_of_text {m : Mem} (h : TextLoaded mText m) : Code.MemcpyLoaded m := by
  have h' : ∀ a b, (a, b) ∈ mText → m[a]? = some b := fun a b hab => h (a, b) hab
  unfold Code.MemcpyLoaded Code.memcpyChunk0 Code.memcpyChunk1 Code.memcpyChunk2
    Code.memcpyChunk3 Code.memcpyChunk4
  repeat' apply And.intro
  all_goals (apply h'; decide)

/-- The owned registers of a `memcpy` run: the PC, `ra`, `a0-a7`, `t0`, `t1`,
`t3-t6`. -/
abbrev mRegs : List Nat := [VsaIris.PC, 1, 10, 11, 12, 13, 14, 15, 16, 17, 5, 6, 28, 29, 30, 31]

/-- The read-only source bytes `[X, X + n)` at the image `img`. -/
def srcText (X n : Nat) (img : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  (List.range n).map fun k => (X + k, img (X + k))

theorem mem_srcText {X n : Nat} {img : Nat → BitVec 8} {p : Nat × BitVec 8}
    (h : p ∈ srcText X n img) : X ≤ p.1 ∧ p.1 < X + n ∧ p.2 = img p.1 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hk
  exact ⟨by simp, by simp; omega, rfl⟩

/-- A source byte reads its image value. -/
theorem srcRead {X n : Nat} {img : Nat → BitVec 8} {m : Mem} (hD : DataReads (srcText X n img) m)
    {b : Nat} (hb : X ≤ b ∧ b < X + n) : (m[b]?).getD 0 = img b := by
  have := hD (b, img b) (by
    refine List.mem_map.mpr ⟨b - X, List.mem_range.mpr (by omega), ?_⟩
    simp only [Prod.mk.injEq]; constructor <;> congr 1 <;> omega)
  exact this

/-! ## The run predicate -/

/-- **`memcpy`'s run at a symbolic state**: one fuel bound under which every
matching state runs to `Q`, reading the code and the source read-only. -/
def MW (live : Nat → Prop) (X n : Nat) (img : Nat → BitVec 8) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (pc : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) : Prop :=
  ∃ N, ∀ rv mv, Matches mRegs S pc R Mt rv mv →
    LocalRun (vsaModel live) [] (mText ++ srcText X n img) mRegs S Q N rv mv

section MW

variable {live : Nat → Prop} {X n : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem mw_done {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : ∀ rv mv, Matches mRegs S pc R Mt rv mv → Q rv mv) : MW live X n img S Q pc R Mt :=
  ⟨0, h⟩

theorem mw_congr {pc : BitVec 64} {R R' : Nat → BitVec 64} {Mt : Mem}
    (hR : ∀ r ∈ mRegs, r ≠ VsaIris.PC → R' r = R r) (h : MW live X n img S Q pc R' Mt) :
    MW live X n img S Q pc R Mt := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun rv mv hm => hN rv mv
    ⟨hm.pc, fun r hr hne => (hm.regs r hr hne).trans (hR r hr hne).symm, hm.img⟩⟩

theorem mw_congr_mem {pc : BitVec 64} {R : Nat → BitVec 64} {Mt Mt' : Mem}
    (hM : ∀ a, S a → imgM Mt' a = imgM Mt a) (h : MW live X n img S Q pc R Mt') :
    MW live X n img S Q pc R Mt := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun rv mv hm => hN rv mv ⟨hm.pc, hm.regs, fun a ha => (hm.img a ha).trans (hM a ha).symm⟩⟩

theorem mw_pc {pc pc' : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} (e : pc = pc')
    (h : MW live X n img S Q pc' R Mt) : MW live X n img S Q pc R Mt := e ▸ h

/-- `swp_segLD` with no read-only register, over `mText ++ srcText`. -/
theorem mw_segL {pc0 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (LD W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 (keysG L) bs)
    (hkeys : KeysOK (keysG L)) (hwr : ∀ x ∈ wrChain bs, x ∈ keysG L)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs L lds).log a)
    (hlive : ∀ p ∈ mText, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded mText m → DataReads (srcText X n img) m →
      (∀ a ∈ LD, (m[a]?).getD 0 = imgM Mt a) → ChainFacts m m L lds bs)
    (hL : ∀ p ∈ L, p.1 ∈ mRegs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2)
    (hLD : ∀ a ∈ LD, S a) (hW : ∀ a ∈ W, S a)
    (hk : MW live X n img S Q (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
      (fun r => if r ∈ keysG L then finReg bs L lds r else R r)
      (writeLog Mt (segOut bs L lds).log)) :
    MW live X n img S Q pc0 R Mt := by
  obtain ⟨N, hN⟩ := hk
  refine ⟨N + 1, fun rv mv hm => .inr ⟨k, segFrom_of_runFact
    (seg_runFact live bs L lds pc0
      (textMRof (mText ++ srcText X n img) ++ LD.map fun a => (a, DFrac.own 1, imgM Mt a))
      (W.map fun a => (a, imgM Mt a)) k hlen hwf hkeys hwr ?_ ?_)
    (fun p hp => by cases hp) ?_ ?_ ?_ ?_⟩⟩
  · intro a ha
    exact hcover a fun hW' => ha _ (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hW') rfl
  · intro c hok hfoot
    obtain ⟨_, hMR, _, _⟩ := hfoot
    have hT : TextLoaded mText c.σ.mem := by
      have h := code_present hok (textMRof mText)
        (fun q hq => hMR q (List.mem_append_left _ (by
          simp only [textMRof, List.map_append]; exact List.mem_append_left _ hq)))
        (fun q hq => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
          exact hlive p hp)
      intro p hp
      exact h _ (List.mem_map_of_mem (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hp)
    have hD : DataReads (srcText X n img) c.σ.mem := fun p hp =>
      hMR (p.1, DFrac.discard, p.2) (List.mem_append_left _ (by
        simp only [textMRof, List.map_append]
        exact List.mem_append_right _
          (List.mem_map_of_mem (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hp)))
    refine hfacts c.σ.mem hT hD fun a ha => ?_
    exact hMR (a, DFrac.own 1, imgM Mt a) (List.mem_append_right _
      (List.mem_map_of_mem (f := fun a => (a, DFrac.own 1, imgM Mt a)) ha))
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact .inl hq
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact .inr ⟨hLD a ha, hm.img a (hLD a ha)⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl ⟨List.mem_cons_self, hm.pc⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨h1, h2, h3⟩ := hL q hq
      exact .inl ⟨h1, (hm.regs _ h1 h2).trans h3⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact ⟨hW a ha, hm.img a (hW a ha)⟩
  · intro rv' mv' h1 h2 h3 h4
    refine hN rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hkL : r ∈ keysG L
      · rw [ite_eq_left_iff.2 (fun h => absurd hkL h)]
        obtain ⟨v, hv⟩ := (mem_keysG_iff r L).1 hkL
        exact h1 _ (List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun p => (p.1, p.2, finReg bs L lds p.1)) hv))
      · rw [ite_eq_right_iff.2 (fun h => absurd h hkL)]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        rcases List.mem_cons.mp hp with rfl | hp
        · exact fun e => hne e.symm
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact fun e => hkL ((mem_keysG_iff r L).2 ⟨q.2, by rw [← e]; exact hq⟩)
    · by_cases hw : a ∈ W
      · have := h3 _ (List.mem_map_of_mem
          (f := fun p => (p.1, p.2, ((writeLog (wbase (W.map fun a => (a, imgM Mt a)))
            (segOut bs L lds).log)[p.1]?).getD 0))
          (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hw))
        refine this.trans (writeLog_getD_congr _ _ _ _ ?_)
        obtain ⟨o', ho', hg⟩ := wbase_get (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hw)
        show ((wbase (W.map fun a => (a, imgM Mt a)))[a]?).getD 0 = (Mt[a]?).getD 0
        rw [hg]
        obtain ⟨b, _, e⟩ := List.mem_map.mp ho'
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · rw [h4 a ha fun p hp => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
          exact fun e => hw (e ▸ hc)]
        rw [hm.img a ha]
        unfold imgM
        rw [writeLog_out _ _ _ (hcover a hw)]

/-- **One reflected segment of a `memcpy` run** (`swp_stepD`'s shape, no `gp`). -/
theorem mw_step {pc0 pc1 : BitVec 64} {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (bs : List BBlock) (ks : List Nat) (lds : List (List (BitVec 8)))
    (LD W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 ks bs)
    (hkeys : KeysOK ks) (hwr : ∀ x ∈ wrChain bs, x ∈ ks)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs (pinsOf ks R) lds).log a)
    (hlive : ∀ p ∈ mText, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded mText m → DataReads (srcText X n img) m →
      (∀ a ∈ LD, (m[a]?).getD 0 = imgM Mt a) → ChainFacts m m (pinsOf ks R) lds bs)
    (hks : ∀ x ∈ ks, x ∈ mRegs ∧ x ≠ VsaIris.PC ∧ x ≠ gp)
    (hLD : ∀ a ∈ LD, S a) (hW : ∀ a ∈ W, S a)
    (hpc : evalBlocksPC pc0 (SegEvalState.init (pinsOf ks R) lds) bs = pc1)
    (hR : ∀ x ∈ ks, x ≠ gp → finReg bs (pinsOf ks R) lds x = R' x)
    (hRo : ∀ x ∈ mRegs, x ≠ VsaIris.PC → x ∉ ks → R' x = R x)
    (hMt : writeLog Mt (segOut bs (pinsOf ks R) lds).log = Mt')
    (hk : MW live X n img S Q pc1 R' Mt') :
    MW live X n img S Q pc0 R Mt := by
  have hK := keysG_pinsOf R ks
  refine mw_segL bs (pinsOf ks R) lds LD W k hlen (by rw [hK]; exact hwf) (by rw [hK]; exact hkeys)
    (fun x hx => by rw [hK]; exact hwr x hx) hcover hlive hfacts (fun p hp => ?_) hLD hW ?_
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3⟩ := hks x hx
    exact ⟨h1, h2, by simp [h3]⟩
  · rw [hK, hpc, hMt]
    refine mw_congr (fun r hr hne => ?_) hk
    by_cases hk' : r ∈ ks
    · rw [ite_eq_left_iff.2 (fun h => absurd hk' h)]
      exact (hR r hk' (hks r hk').2.2).symm
    · rw [ite_eq_right_iff.2 (fun h => absurd h hk')]
      exact hRo r hr hne hk'

/-- **An observed ALU step of a `memcpy` run** (`swp_aluRR` without `gp`). -/
theorem mw_alu {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (i : Nat) (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (rd : Nat) (val : BitVec 64) (hexec : AluStep live i RR MR rd val)
    (hMR : ∀ p ∈ MR, (p.1, p.2.2) ∈ mText ++ srcText X n img)
    (hRR : ∀ p ∈ RR, p.1 ∈ mRegs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2.2)
    (hrd : rd ∈ mRegs) (hpc : pc = BitVec.ofNat 64 i)
    (hk : MW live X n img S Q (BitVec.ofNat 64 (i + 4)) (upd R rd val) Mt) :
    MW live X n img S Q pc R Mt := by
  subst hpc
  obtain ⟨N, hN⟩ := hk
  refine ⟨N + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (MW := [])
    (runFact_of_aluStep (old := rv rd) hexec) (fun p hp => ?_) (fun p hp => .inl (hMR p hp)) ?_
    (fun p hp => by cases hp) ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hRR p hp
    exact .inr ⟨h1, by rw [hm.regs _ h1 h2, h3]⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨List.mem_cons_self, hm.pc⟩
    · exact .inl ⟨hrd, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hN rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hr1 : r = rd
      · subst hr1
        rw [upd_same]
        exact h1 (r, rv r, val) (by simp)
      · rw [upd_other _ _ hr1]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hne e.symm
        · exact fun e => hr1 e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]

end MW

/-! ## The `sltiu a2,a2,8` at `0x80006bd8` -/

/-- The code bytes as a read footprint. -/
abbrev mMR : List (Nat × DFrac × BitVec 8) := textMRof mText

theorem mMR_text : ∀ p ∈ mMR, (p.1, p.2.2) ∈ mText := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hq

theorem loaded_of_mMR {m : Mem} (h : ∀ q ∈ mMR, m[q.1]? = some q.2.2) : Code.MemcpyLoaded m :=
  memcpyLoaded_of_text fun _ hp =>
    h _ (List.mem_map_of_mem (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hp)

theorem sltiuAluStep {live : Nat → Prop} (hlive : ∀ p ∈ mText, live p.1) (v12 : BitVec 64) :
    AluStep live 0x80006bd8 [(12, DFrac.own 1, v12)] mMR 12
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12))))) :=
  aluStep_of_obs (by decide) (by decide)
    (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; exact ⟨by simp, by simp⟩)
    (fun q hq => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq; exact hlive p hp)
    (fun c hG ht hpc hRR hMR => by
      obtain ⟨vm, hvm⟩ := hG.minstret
      obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
        site_80006bd8 c.σ c.tick c.steps _ vm v12 hG hpc hvm (hRR _ List.mem_cons_self)
          (loaded_of_mMR hMR) rfl ht
      exact ⟨σ', i', vm, hs, hi', hG', hmem, hobs⟩)

theorem mst_80006bd8 {live : Nat → Prop} {X n : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live X n img S Q 0x80006bdc#64
      (upd R 12 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (R 12) (sign_extend (m := 64) (0x008#12)))))) Mt) :
    MW live X n img S Q 0x80006bd8#64 R Mt :=
  mw_alu 0x80006bd8 _ _ 12 _ (sltiuAluStep hlive (R 12))
    (fun p hp => List.mem_append_left _ (mMR_text p hp))
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; exact ⟨by simp, by simp [VsaIris.PC], rfl⟩)
    (by decide) rfl hk

end VsaIris.Memcpy

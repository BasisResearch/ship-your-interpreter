import VsaIris.Vsa.RunBase
import VsaIris.Vsa.Tools
import Vsa.Sim.InterpSpillReads

/-!
# Symbolic execution over local runs

`SWP pc R Mt` is the weakest precondition of a `LocalRun` at a symbolic
state:

* the program counter `pc`;
* a register file `R`, read on the owned registers other than `PC`;
* a tracking memory `Mt`, whose total read is the owned bytes' image.

Every concrete state matching it runs to `Q` within one fuel bound. A reflected
segment (`segEval_sound` through `seg_runFact`) is one step of `SWP` (`swp_seg`).
The generated per-instruction lemmas (`AllocSteps.lean`, from
`scripts/gen_alloc_steps.py`) are its instances. Their continuations are the
successor's symbolic state, so a path through a function is a chain of
lemma applications, and a loop is an induction whose motive is `SWP`.

The fuel bound sits outside the state quantifier: `SegFrom`'s continuation
fixes it before the successor state is known. Branches join two bounds by
`LocalRun.fuel_mono`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The listed code bytes are present in a memory. -/
def TextLoaded (text : List (Nat × BitVec 8)) (m : Mem) : Prop :=
  ∀ p ∈ text, m[p.1]? = some p.2

/-- Code bytes as read-only footprint cells. -/
abbrev textMRof (text : List (Nat × BitVec 8)) : List (Nat × DFrac × BitVec 8) :=
  text.map fun p => (p.1, DFrac.discard, p.2)

theorem textLoaded_of_foot {live : Nat → Prop} {text : List (Nat × BitVec 8)} {c : Config}
    (hok : VsaOk live c) (hlive : ∀ p ∈ text, live p.1)
    {LD : List (Nat × DFrac × BitVec 8)}
    (hmr : ∀ p ∈ textMRof text ++ LD, (vsaModel live).mem c p.1 = p.2.2) :
    TextLoaded text c.σ.mem := by
  have h := code_present hok (textMRof text) (fun q hq => hmr q (List.mem_append_left _ hq))
    (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact hlive p hp)
  intro p hp
  exact h _ (List.mem_map_of_mem (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hp)

section Fuel

variable {M : MachineModel} {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
  {rs : List Nat} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- More fuel never hurts. -/
theorem LocalRun.fuel_succ : ∀ {n : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8},
    LocalRun M ro text rs S Q n rv mv → LocalRun M ro text rs S Q (n + 1) rv mv
  | 0, _, _, h => .inl h
  | _ + 1, _, _, h => h.imp id fun ⟨k, hk⟩ => ⟨k, hk.mono fun _ _ h' => LocalRun.fuel_succ h'⟩

theorem LocalRun.fuel_mono {n n' : Nat} (hle : n ≤ n') {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} (h : LocalRun M ro text rs S Q n rv mv) :
    LocalRun M ro text rs S Q n' rv mv := by
  induction hle with
  | refl => exact h
  | step _ ih => exact LocalRun.fuel_succ ih

end Fuel

theorem mem_keysG_iff (r : Nat) : ∀ L : GRegs, r ∈ keysG L ↔ ∃ v, (r, v) ∈ L
  | [] => by simp [keysG]
  | (k, w) :: L => by
    simp only [keysG, List.mem_cons, mem_keysG_iff r L, Prod.mk.injEq]
    constructor
    · rintro (rfl | ⟨v, hv⟩)
      · exact ⟨w, .inl ⟨rfl, rfl⟩⟩
      · exact ⟨v, .inr hv⟩
    · rintro ⟨v, ⟨rfl, rfl⟩ | hv⟩
      · exact .inl rfl
      · exact .inr ⟨v, hv⟩

/-- A register file updated at one register. -/
def upd (R : Nat → BitVec 64) (k : Nat) (v : BitVec 64) (r : Nat) : BitVec 64 :=
  if r = k then v else R r

@[simp] theorem upd_same (R : Nat → BitVec 64) (k : Nat) (v : BitVec 64) : upd R k v k = v := by
  simp [upd]

theorem upd_other (R : Nat → BitVec 64) {k r : Nat} (v : BitVec 64) (h : r ≠ k) :
    upd R k v r = R r := by
  simp [upd, h]

/-- The pins of a register list read off a register file; `gp` reads its
fixed value. -/
def pinsOf (ks : List Nat) (R : Nat → BitVec 64) : GRegs :=
  ks.map fun k => (k, if k = gp then gpV else R k)

theorem keysG_pinsOf (R : Nat → BitVec 64) : ∀ ks : List Nat, keysG (pinsOf ks R) = ks
  | [] => rfl
  | k :: ks => by simp only [pinsOf, List.map_cons, keysG]; rw [← pinsOf, keysG_pinsOf R ks]


/-! ## Values the step table names -/

/-- `n` bytes of an image from `a`, in address order (a load's byte list). -/
def bytesAt (f : Nat → BitVec 8) (a n : Nat) : List (BitVec 8) :=
  (List.range n).map fun j => f (a + j)

/-- The value a load of kind `k` reads from the tracking memory at `a`. -/
abbrev ldv (k : MKind) (Mt : Mem) (a : Nat) : BitVec 64 :=
  bytesVal k (bytesAt (imgM Mt) a (widthOfM k))

/-- A 32-bit result, sign-extended (the `*w` instructions). -/
abbrev sx32 (v : BitVec 64) : BitVec 64 := BitVec.signExtend 64 (v.truncate 32)

/-- `slti`'s and `slt`'s result (the Sail form). -/
abbrev sltiV (a b : BitVec 64) : BitVec 64 := zero_extend (m := 64) (bool_to_bit (zopz0zI_s a b))
abbrev sltV (a b : BitVec 64) : BitVec 64 := zero_extend (m := 64) (bool_to_bit (zopz0zI_s a b))

/-- The owned byte addresses of an access of width `w` at `a`. -/
def accAddrs (a w : Nat) : List Nat := (List.range w).map (a + ·)

theorem mem_accAddrs {a w j : Nat} (hj : j < w) : a + j ∈ accAddrs a w :=
  List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem of_mem_accAddrs {a w b : Nat} (h : b ∈ accAddrs a w) : a ≤ b ∧ b < a + w := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hj
  omega

/-- Bytes outside an access are outside its one-entry log. -/
theorem outL_single {a w b : Nat} (v : BitVec 64) (h : b ∉ accAddrs a w) : OutL [(a, w, v)] b := by
  refine ⟨?_, trivial⟩
  refine Classical.byContradiction fun hc => h ?_
  have hc' : a ≤ b ∧ b < a + w := by simp only at hc; omega
  have : b - a < w := by omega
  have e : a + (b - a) = b := by omega
  rw [← e]
  exact mem_accAddrs this

theorem bytesAt_getD (f : Nat → BitVec 8) (a : Nat) {n j : Nat} (h : j < n) :
    (bytesAt f a n).getD j 0#8 = f (a + j) := by
  simp [bytesAt, h]

theorem lpins8_img {m : Mem} {Mt : Mem} {a : Nat}
    (h : ∀ b ∈ accAddrs a 8, (m[b]?).getD 0 = imgM Mt b) :
    LPins8 m a (bytesAt (imgM Mt) a 8) := by
  have g := fun j (hj : j < 8) => (h _ (mem_accAddrs hj)).trans (bytesAt_getD (imgM Mt) a hj).symm
  exact ⟨by simpa using g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega),
    g 4 (by omega), g 5 (by omega), g 6 (by omega), g 7 (by omega)⟩

theorem lpins4_img {m : Mem} {Mt : Mem} {a : Nat}
    (h : ∀ b ∈ accAddrs a 4, (m[b]?).getD 0 = imgM Mt b) :
    LPins4 m a (bytesAt (imgM Mt) a 4) := by
  have g := fun j (hj : j < 4) => (h _ (mem_accAddrs hj)).trans (bytesAt_getD (imgM Mt) a hj).symm
  exact ⟨by simpa using g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega)⟩

theorem lpins1_img {m : Mem} {Mt : Mem} {a : Nat}
    (h : ∀ b ∈ accAddrs a 1, (m[b]?).getD 0 = imgM Mt b) :
    (m[a]?).getD 0 = (bytesAt (imgM Mt) a 1).getD 0 0#8 := by
  have := (h _ (mem_accAddrs (j := 0) (by omega))).trans (bytesAt_getD (imgM Mt) a (n := 1) (by omega)).symm
  simpa using this

theorem lpins2_img {m : Mem} {Mt : Mem} {a : Nat}
    (h : ∀ b ∈ accAddrs a 2, (m[b]?).getD 0 = imgM Mt b) :
    (m[a]?).getD 0 = (bytesAt (imgM Mt) a 2).getD 0 0#8 ∧
      (m[a + 1]?).getD 0 = (bytesAt (imgM Mt) a 2).getD 1 0#8 :=
  by
    have h0 := (h _ (mem_accAddrs (j := 0) (by omega))).trans
      (bytesAt_getD (imgM Mt) a (n := 2) (by omega)).symm
    exact ⟨by simpa using h0, (h _ (mem_accAddrs (j := 1) (by omega))).trans
      (bytesAt_getD (imgM Mt) a (n := 2) (by omega)).symm⟩


/-- A load's address side conditions (`MemFacts`' first conjunct): RAM, off
the HTIF words. -/
abbrev LdOK (ea w : Nat) : Prop :=
  0x80000000 ≤ ea ∧ ea + w ≤ 0x100000000 ∧ (ea + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ ea)

/-- An aligned store's address side conditions (`sd`, `sw`, `sh`). -/
abbrev StOK (ea w : Nat) : Prop :=
  0x80000000 ≤ ea ∧ ea + w ≤ 0x100000000 ∧ tohostAddr + 16 ≤ ea ∧ ea % w = 0

/-- A byte store's address side conditions (`sb`). -/
abbrev StOKb (ea : Nat) : Prop :=
  0x80000000 ≤ ea ∧ ea + 1 ≤ 0x100000000 ∧ tohostAddr + 16 ≤ ea


/-! ## The tracking memory -/

theorem read64_bytes_present {m : Mem} {a v : Nat} (h : read64 m a = some v) :
    ∀ k, k < 8 → m[a + k]? = some (imgM m (a + k)) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := read64_bytes m a v h
  intro k hk
  unfold imgM
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first
    | (simp only [Nat.add_zero]; rw [h0]; rfl)
    | (rw [h1]; rfl) | (rw [h2]; rfl) | (rw [h3]; rfl) | (rw [h4]; rfl) | (rw [h5]; rfl)
    | (rw [h6]; rfl) | (rw [h7]; rfl) | omega

/-- A doubleword load reads what `read64` reads. -/
theorem ldv_ld {Mt : Mem} {a : Nat} {v : BitVec 64} (h : read64 Mt a = some v.toNat) :
    ldv .ld Mt a = v :=
  wordOf_value (f := imgM Mt) (read64_bytes_present h) h

/-- A load's bytes are untouched by a disjoint store. -/
theorem ldv_store_miss (k : MKind) (Mt : Mem) {a b w : Nat} (v : BitVec 64)
    (h : a + widthOfM k ≤ b ∨ b + w ≤ a) :
    ldv k (writeLog Mt [(b, w, v)]) a = ldv k Mt a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  unfold imgM
  rw [writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩)]

/-- A doubleword load reads a doubleword just stored at its address. -/
theorem ldv_store_hit (Mt : Mem) (a : Nat) (v : BitVec 64) :
    ldv .ld (writeLog Mt [(a, 8, v)]) a = v :=
  ldv_ld (read64_of_writeLog_at Mt [(a, 8, v)] 0 a v rfl trivial)

theorem read64_logOut {m : Mem} {w : List WEntry} {a : Nat}
    (h : ∀ k, k < 8 → OutL w (a + k)) : read64 (writeLog m w) a = read64 m a :=
  (read64_agreeP (P := OutL w) (fun k hk => (writeLog_out m w k hk).symm) h).symm

/-- `read64` through a disjoint store. -/
theorem read64_store_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 8 ≤ b ∨ b + w ≤ a) :
    read64 (writeLog Mt [(b, w, v)]) a = read64 Mt a :=
  read64_logOut fun k hk => by simp only [OutL]; exact ⟨by omega, trivial⟩

/-- `read64` of a doubleword just stored. -/
theorem read64_store_hit (Mt : Mem) (a : Nat) (v : BitVec 64) :
    read64 (writeLog Mt [(a, 8, v)]) a = some v.toNat :=
  read64_of_writeLog_at Mt [(a, 8, v)] 0 a v rfl trivial

/-- The image through a store, off its bytes. -/
theorem imgM_store_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a < b ∨ b + w ≤ a) :
    imgM (writeLog Mt [(b, w, v)]) a = imgM Mt a := by
  unfold imgM
  rw [writeLog_out _ _ _ (by simp only [OutL]; exact ⟨h, trivial⟩)]

/-! ## Branch guards -/

theorem guard_beq (a b : BitVec 64) : guardB .BEQ a b = true ↔ a = b := by
  simp [guardB]

theorem guard_bne (a b : BitVec 64) : guardB .BNE a b = true ↔ a ≠ b := by
  simp [guardB]

theorem guard_bltu (a b : BitVec 64) : guardB .BLTU a b = true ↔ a.toNat < b.toNat := by
  simp only [guardB]; exact ult_iff a b

theorem guard_bgeu (a b : BitVec 64) : guardB .BGEU a b = true ↔ b.toNat ≤ a.toNat := by
  simp only [guardB]; exact uge_iff a b

theorem guard_blt (a b : BitVec 64) : guardB .BLT a b = true ↔ a.toInt < b.toInt := by
  simp [guardB, zopz0zI_s]

theorem guard_bge (a b : BitVec 64) : guardB .BGE a b = true ↔ b.toInt ≤ a.toInt := by
  simp [guardB, zopz0zKzJ_s]

theorem guard_false {op : bop} {a b : BitVec 64} {P : Prop} (h : guardB op a b = true ↔ P) :
    guardB op a b = false ↔ ¬ P := by
  rw [← h]; simp

section SWP

variable (live : Nat → Prop) (text : List (Nat × BitVec 8)) (rs : List Nat) (S : Nat → Prop)
  (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)

/-- The states a symbolic state stands for. -/
structure Matches (pc : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = pc
  regs : ∀ r ∈ rs, r ≠ VsaIris.PC → rv r = R r
  img : ∀ a, S a → mv a = imgM Mt a

/-- **The weakest precondition at a symbolic state**: one fuel bound under which
every matching state runs to `Q`. -/
def SWP (pc : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) : Prop :=
  ∃ n, ∀ rv mv, Matches rs S pc R Mt rv mv →
    LocalRun (vsaModel live) roR text rs S Q n rv mv

variable {live text rs S Q}

/-- The run is done: every matching state satisfies `Q`. -/
theorem swp_done {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : ∀ rv mv, Matches rs S pc R Mt rv mv → Q rv mv) : SWP live text rs S Q pc R Mt :=
  ⟨0, h⟩

/-- Only the owned registers other than `PC` matter. -/
theorem swp_congr {pc : BitVec 64} {R R' : Nat → BitVec 64} {Mt : Mem}
    (hR : ∀ r ∈ rs, r ≠ VsaIris.PC → R' r = R r) (h : SWP live text rs S Q pc R' Mt) :
    SWP live text rs S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => hn rv mv ⟨hm.pc, fun r hr hne => (hm.regs r hr hne).trans (hR r hr hne).symm, hm.img⟩⟩

/-- Only the owned bytes of the tracking memory matter. -/
theorem swp_congr_mem {pc : BitVec 64} {R : Nat → BitVec 64} {Mt Mt' : Mem}
    (hM : ∀ a, S a → imgM Mt' a = imgM Mt a) (h : SWP live text rs S Q pc R Mt') :
    SWP live text rs S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => hn rv mv ⟨hm.pc, hm.regs, fun a ha => (hm.img a ha).trans (hM a ha).symm⟩⟩

/-- A case split on a pure fact. -/
theorem swp_cases {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} (P : Prop)
    (h1 : P → SWP live text rs S Q pc R Mt) (h2 : ¬ P → SWP live text rs S Q pc R Mt) :
    SWP live text rs S Q pc R Mt := by
  by_cases h : P
  · exact h1 h
  · exact h2 h

/-- One reflected segment over an arbitrary pin list `L` (the core of
`swp_seg`). -/
theorem swp_segL {pc0 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (LD W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 (keysG L) bs)
    (hkeys : KeysOK (keysG L)) (hwr : ∀ x ∈ wrChain bs, x ∈ keysG L)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs L lds).log a)
    (hlive : ∀ p ∈ text, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded text m → (∀ a ∈ LD, (m[a]?).getD 0 = imgM Mt a) →
      ChainFacts m m L lds bs)
    (hPC : VsaIris.PC ∈ rs)
    (hL : ∀ p ∈ L, (p.1 ∈ rs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2) ∨
      ((p.1, p.2) ∈ roR ∧ finReg bs L lds p.1 = p.2))
    (hLD : ∀ a ∈ LD, S a) (hW : ∀ a ∈ W, S a)
    (hk : SWP live text rs S Q (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
      (fun r => if r ∈ keysG L then finReg bs L lds r else R r)
      (writeLog Mt (segOut bs L lds).log)) :
    SWP live text rs S Q pc0 R Mt := by
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨k, segFrom_of_runFact
    (seg_runFact live bs L lds pc0 (textMRof text ++ LD.map fun a => (a, DFrac.own 1, imgM Mt a))
      (W.map fun a => (a, imgM Mt a)) k hlen hwf hkeys hwr ?_ ?_)
    (fun p hp => by cases hp) ?_ ?_ ?_ ?_⟩⟩
  · intro a ha
    exact hcover a fun hW' => ha _ (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hW') rfl
  · intro c hok hfoot
    obtain ⟨_, hMR, _, _⟩ := hfoot
    refine hfacts c.σ.mem (textLoaded_of_foot hok hlive hMR) fun a ha => ?_
    have := hMR (a, DFrac.own 1, imgM Mt a) (List.mem_append_right _
      (List.mem_map_of_mem (f := fun a => (a, DFrac.own 1, imgM Mt a)) ha))
    exact this
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact .inl hq
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact .inr ⟨hLD a ha, hm.img a (hLD a ha)⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl ⟨hPC, hm.pc⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      rcases hL q hq with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, (hm.regs _ h1 h2).trans h3⟩
      · exact .inr ⟨h1, h2⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact ⟨hW a ha, hm.img a (hW a ha)⟩
  · intro rv' mv' h1 h2 h3 h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
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


/-- **One reflected segment.** `seg_step` over an arbitrary code list: the
pins are the registers `ks` read off `R` (`gp` at its fixed value), the loaded
(`LD`) and written (`W`) owned bytes are read off the tracking memory, and the
successor state is computed from the segment. -/
theorem swp_seg {pc0 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (bs : List BBlock) (ks : List Nat) (lds : List (List (BitVec 8)))
    (LD W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 ks bs)
    (hkeys : KeysOK ks) (hwr : ∀ x ∈ wrChain bs, x ∈ ks)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs (pinsOf ks R) lds).log a)
    (hlive : ∀ p ∈ text, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded text m → (∀ a ∈ LD, (m[a]?).getD 0 = imgM Mt a) →
      ChainFacts m m (pinsOf ks R) lds bs)
    (hPC : VsaIris.PC ∈ rs)
    (hks : ∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC))
    (hgp : gp ∈ ks → finReg bs (pinsOf ks R) lds gp = gpV)
    (hLD : ∀ a ∈ LD, S a) (hW : ∀ a ∈ W, S a)
    (hk : SWP live text rs S Q (evalBlocksPC pc0 (SegEvalState.init (pinsOf ks R) lds) bs)
      (fun r => if r ∈ ks then finReg bs (pinsOf ks R) lds r else R r)
      (writeLog Mt (segOut bs (pinsOf ks R) lds).log)) :
    SWP live text rs S Q pc0 R Mt := by
  have hK := keysG_pinsOf R ks
  refine swp_segL bs (pinsOf ks R) lds LD W k hlen (by rw [hK]; exact hwf) (by rw [hK]; exact hkeys)
    (fun x hx => by rw [hK]; exact hwr x hx) hcover hlive hfacts hPC (fun p hp => ?_) hLD hW (by rw [hK]; exact hk)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  by_cases hg : x = gp
  · subst hg
    exact .inr ⟨by simp [roR], by simpa using hgp hx⟩
  · rcases hks x hx with h | ⟨h1, h2⟩
    · exact absurd h hg
    · exact .inl ⟨h1, h2, by simp [hg]⟩


/-- **One `jal`** (a call): the link register takes the return address and
the run continues at the target. -/
theorem swp_jal {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (i : Nat) (code : List (BitVec 8)) (tgt : BitVec 64)
    (hexec : JalExec (vsaModel live) i code tgt)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ text)
    (hPC : VsaIris.PC ∈ rs) (hra : VsaIris.ra ∈ rs) (hpc : pc = BitVec.ofNat 64 i)
    (hk : SWP live text rs S Q tgt (upd R VsaIris.ra (BitVec.ofNat 64 (i + 4))) Mt) :
    SWP live text rs S Q pc R Mt := by
  subst hpc
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (RR := []) (MW := [])
    (RW := [(VsaIris.PC, BitVec.ofNat 64 i, tgt),
      (VsaIris.ra, rv VsaIris.ra, BitVec.ofNat 64 (i + 4))])
    (fun σ hok hf => by
      obtain ⟨σ', hs, hok', hloc⟩ := hexec (rv VsaIris.ra) σ hok hf
      exact ⟨σ', .succ hs (.zero _), hok', hloc⟩)
    (fun p hp => by cases hp) (fun p hp => .inl (hcode p hp)) ?_ (fun p hp => by cases hp) ?_⟩⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨hPC, hm.pc⟩
    · exact .inl ⟨hra, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hr1 : r = VsaIris.ra
      · subst hr1
        rw [upd_same]
        exact h1 (VsaIris.ra, rv VsaIris.ra, BitVec.ofNat 64 (i + 4)) (by simp)
      · rw [upd_other _ _ hr1]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hne e.symm
        · exact fun e => hr1 e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]


/-- **One reflected segment, successor named.** `swp_seg` with the successor
state given: each pinned register's final value (`finReg` on the left, the
orientation the kernel checks fast), the unpinned owned registers unchanged,
the end PC and the memory after the log. -/
theorem swp_step {pc0 pc1 : BitVec 64} {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (bs : List BBlock) (ks : List Nat) (lds : List (List (BitVec 8)))
    (LD W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 ks bs)
    (hkeys : KeysOK ks) (hwr : ∀ x ∈ wrChain bs, x ∈ ks)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs (pinsOf ks R) lds).log a)
    (hlive : ∀ p ∈ text, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded text m → (∀ a ∈ LD, (m[a]?).getD 0 = imgM Mt a) →
      ChainFacts m m (pinsOf ks R) lds bs)
    (hPC : VsaIris.PC ∈ rs)
    (hks : ∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC))
    (hgp : gp ∈ ks → finReg bs (pinsOf ks R) lds gp = gpV) (hgprs : gp ∉ rs)
    (hLD : ∀ a ∈ LD, S a) (hW : ∀ a ∈ W, S a)
    (hpc : evalBlocksPC pc0 (SegEvalState.init (pinsOf ks R) lds) bs = pc1)
    (hR : ∀ x ∈ ks, x ≠ gp → finReg bs (pinsOf ks R) lds x = R' x)
    (hRo : ∀ x ∈ rs, x ≠ VsaIris.PC → x ∉ ks → R' x = R x)
    (hMt : writeLog Mt (segOut bs (pinsOf ks R) lds).log = Mt')
    (hk : SWP live text rs S Q pc1 R' Mt') :
    SWP live text rs S Q pc0 R Mt := by
  refine swp_seg bs ks lds LD W k hlen hwf hkeys hwr hcover hlive hfacts hPC hks hgp hLD hW ?_
  rw [hpc, hMt]
  refine swp_congr (fun r hr hne => ?_) hk
  by_cases hk' : r ∈ ks
  · rw [ite_eq_left_iff.2 (fun h => absurd hk' h)]
    by_cases hg : r = gp
    · subst hg; exact absurd hr hgprs
    · exact (hR r hk' hg).symm
  · rw [ite_eq_right_iff.2 (fun h => absurd h hk')]
    exact hRo r hr hne hk'

end SWP

end VsaIris.Sym

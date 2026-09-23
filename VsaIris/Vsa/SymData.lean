import VsaIris.Vsa.SymRun

/-!
# Symbolic runs that read persistent data

`SWP` (`SymRun.lean`) reads two kinds of bytes: the code `text`, which must be
`live` (a fetch needs the byte PRESENT, `BytePinsM`), and the owned bytes `S`.
The interpreter's runs also read immutable data that is neither: AST nodes,
C strings and closure objects are persistent `↦ₘ□` (INTERP_DESIGN.md §3), and
a load only needs the byte's total read (`LPins*`, the model's `getD 0`).

So the read-only list of an interpreter run is `T ++ D`: the code `T` (live)
and the data `D` (persistent, no liveness). `swp_segD`/`swp_stepD` are
`swp_segL`/`swp_step` with that split; every other `SWP` lemma applies
unchanged, because `SWP` itself does not care where its `text` comes from.

`swp_havoc` is a load whose bytes the run does NOT own: the successor's
register holds whatever the byte reads, and the continuation must hold for
every value. `eval_expr` reads an AST node's line field this way
(`0x80003524 lw s0,4(s0)`); `ExprReprWithin`'s read set does not cover it, and
nothing on the path consumes the value.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The listed data bytes read as given (total reads, no presence). -/
def DataReads (D : List (Nat × BitVec 8)) (m : Mem) : Prop :=
  ∀ p ∈ D, (m[p.1]?).getD 0 = p.2

/-- A data view as a read-only list: the addresses `DA` of a memory `Dt`. -/
abbrev dataOf (Dt : Mem) (DA : List Nat) : List (Nat × BitVec 8) :=
  DA.map fun a => (a, imgM Dt a)

theorem dataReads_view {Dt m : Mem} {DA : List Nat} (h : DataReads (dataOf Dt DA) m) :
    ∀ a ∈ DA, (m[a]?).getD 0 = imgM Dt a := fun a ha =>
  h (a, imgM Dt a) (List.mem_map_of_mem (f := fun a => (a, imgM Dt a)) ha)

theorem lpins8_view {m Dt : Mem} {DA : List Nat} {a : Nat} (hD : DataReads (dataOf Dt DA) m)
    (h : ∀ b ∈ accAddrs a 8, b ∈ DA) : LPins8 m a (bytesAt (imgM Dt) a 8) :=
  lpins8_img fun b hb => dataReads_view hD b (h b hb)

theorem lpins4_view {m Dt : Mem} {DA : List Nat} {a : Nat} (hD : DataReads (dataOf Dt DA) m)
    (h : ∀ b ∈ accAddrs a 4, b ∈ DA) : LPins4 m a (bytesAt (imgM Dt) a 4) :=
  lpins4_img fun b hb => dataReads_view hD b (h b hb)

theorem lpins2_view {m Dt : Mem} {DA : List Nat} {a : Nat} (hD : DataReads (dataOf Dt DA) m)
    (h : ∀ b ∈ accAddrs a 2, b ∈ DA) :
    (m[a]?).getD 0 = (bytesAt (imgM Dt) a 2).getD 0 0#8 ∧
      (m[a + 1]?).getD 0 = (bytesAt (imgM Dt) a 2).getD 1 0#8 :=
  lpins2_img fun b hb => dataReads_view hD b (h b hb)

theorem lpins1_view {m Dt : Mem} {DA : List Nat} {a : Nat} (hD : DataReads (dataOf Dt DA) m)
    (h : ∀ b ∈ accAddrs a 1, b ∈ DA) :
    (m[a]?).getD 0 = (bytesAt (imgM Dt) a 1).getD 0 0#8 :=
  lpins1_img fun b hb => dataReads_view hD b (h b hb)

/-- The value a load of kind `k` reads from a byte function at `a`
(`ldv` is this at `imgM Mt`). -/
abbrev ldvf (k : MKind) (f : Nat → BitVec 8) (a : Nat) : BitVec 64 :=
  bytesVal k (bytesAt f a (widthOfM k))

theorem lpins8_fn {m : Mem} {f : Nat → BitVec 8} {a : Nat}
    (h : ∀ b ∈ accAddrs a 8, (m[b]?).getD 0 = f b) : LPins8 m a (bytesAt f a 8) := by
  have g := fun j (hj : j < 8) => (h _ (mem_accAddrs hj)).trans (bytesAt_getD f a hj).symm
  exact ⟨by simpa using g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega),
    g 4 (by omega), g 5 (by omega), g 6 (by omega), g 7 (by omega)⟩

theorem lpins4_fn {m : Mem} {f : Nat → BitVec 8} {a : Nat}
    (h : ∀ b ∈ accAddrs a 4, (m[b]?).getD 0 = f b) : LPins4 m a (bytesAt f a 4) := by
  have g := fun j (hj : j < 4) => (h _ (mem_accAddrs hj)).trans (bytesAt_getD f a hj).symm
  exact ⟨by simpa using g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega)⟩

theorem lpins2_fn {m : Mem} {f : Nat → BitVec 8} {a : Nat}
    (h : ∀ b ∈ accAddrs a 2, (m[b]?).getD 0 = f b) :
    (m[a]?).getD 0 = (bytesAt f a 2).getD 0 0#8 ∧
      (m[a + 1]?).getD 0 = (bytesAt f a 2).getD 1 0#8 := by
  have h0 := (h _ (mem_accAddrs (j := 0) (by omega))).trans (bytesAt_getD f a (n := 2) (by omega)).symm
  exact ⟨by simpa using h0,
    (h _ (mem_accAddrs (j := 1) (by omega))).trans (bytesAt_getD f a (n := 2) (by omega)).symm⟩

theorem lpins1_fn {m : Mem} {f : Nat → BitVec 8} {a : Nat}
    (h : ∀ b ∈ accAddrs a 1, (m[b]?).getD 0 = f b) :
    (m[a]?).getD 0 = (bytesAt f a 1).getD 0 0#8 := by
  have := (h _ (mem_accAddrs (j := 0) (by omega))).trans (bytesAt_getD f a (n := 1) (by omega)).symm
  simpa using this

section SWPD

variable {live : Nat → Prop} {T D : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- `swp_segL` over a read-only list split into live code `T` and data `D`. -/
theorem swp_segLD {pc0 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (LD W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 (keysG L) bs)
    (hkeys : KeysOK (keysG L)) (hwr : ∀ x ∈ wrChain bs, x ∈ keysG L)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs L lds).log a)
    (hlive : ∀ p ∈ T, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded T m → DataReads D m →
      (∀ a ∈ LD, (m[a]?).getD 0 = imgM Mt a) → ChainFacts m m L lds bs)
    (hPC : VsaIris.PC ∈ rs)
    (hL : ∀ p ∈ L, (p.1 ∈ rs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2) ∨
      ((p.1, p.2) ∈ roR ∧ finReg bs L lds p.1 = p.2))
    (hLD : ∀ a ∈ LD, S a) (hW : ∀ a ∈ W, S a)
    (hk : SWP live (T ++ D) rs S Q (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
      (fun r => if r ∈ keysG L then finReg bs L lds r else R r)
      (writeLog Mt (segOut bs L lds).log)) :
    SWP live (T ++ D) rs S Q pc0 R Mt := by
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨k, segFrom_of_runFact
    (seg_runFact live bs L lds pc0 (textMRof (T ++ D) ++ LD.map fun a => (a, DFrac.own 1, imgM Mt a))
      (W.map fun a => (a, imgM Mt a)) k hlen hwf hkeys hwr ?_ ?_)
    (fun p hp => by cases hp) ?_ ?_ ?_ ?_⟩⟩
  · intro a ha
    exact hcover a fun hW' => ha _ (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hW') rfl
  · intro c hok hfoot
    obtain ⟨_, hMR, _, _⟩ := hfoot
    have hT : TextLoaded T c.σ.mem := by
      have h := code_present hok (textMRof T)
        (fun q hq => hMR q (List.mem_append_left _ (by
          simp only [textMRof, List.map_append]; exact List.mem_append_left _ hq)))
        (fun q hq => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
          exact hlive p hp)
      intro p hp
      exact h _ (List.mem_map_of_mem (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hp)
    have hD : DataReads D c.σ.mem := fun p hp =>
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

/-- **One reflected segment over code and data** (`swp_step` with the split
read-only list). -/
theorem swp_stepD {pc0 pc1 : BitVec 64} {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (bs : List BBlock) (ks : List Nat) (lds : List (List (BitVec 8)))
    (LD W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 ks bs)
    (hkeys : KeysOK ks) (hwr : ∀ x ∈ wrChain bs, x ∈ ks)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs (pinsOf ks R) lds).log a)
    (hlive : ∀ p ∈ T, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded T m → DataReads D m →
      (∀ a ∈ LD, (m[a]?).getD 0 = imgM Mt a) → ChainFacts m m (pinsOf ks R) lds bs)
    (hPC : VsaIris.PC ∈ rs)
    (hks : ∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC))
    (hgp : gp ∈ ks → finReg bs (pinsOf ks R) lds gp = gpV) (hgprs : gp ∉ rs)
    (hLD : ∀ a ∈ LD, S a) (hW : ∀ a ∈ W, S a)
    (hpc : evalBlocksPC pc0 (SegEvalState.init (pinsOf ks R) lds) bs = pc1)
    (hR : ∀ x ∈ ks, x ≠ gp → finReg bs (pinsOf ks R) lds x = R' x)
    (hRo : ∀ x ∈ rs, x ≠ VsaIris.PC → x ∉ ks → R' x = R x)
    (hMt : writeLog Mt (segOut bs (pinsOf ks R) lds).log = Mt')
    (hk : SWP live (T ++ D) rs S Q pc1 R' Mt') :
    SWP live (T ++ D) rs S Q pc0 R Mt := by
  have hK := keysG_pinsOf R ks
  refine swp_segLD bs (pinsOf ks R) lds LD W k hlen (by rw [hK]; exact hwf) (by rw [hK]; exact hkeys)
    (fun x hx => by rw [hK]; exact hwr x hx) hcover hlive hfacts hPC (fun p hp => ?_) hLD hW ?_
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    by_cases hg : x = gp
    · subst hg
      exact .inr ⟨by simp [roR], by simpa using hgp hx⟩
    · rcases hks x hx with h | ⟨h1, h2⟩
      · exact absurd h hg
      · exact .inl ⟨h1, h2, by simp [hg]⟩
  · rw [hK, hpc, hMt]
    refine swp_congr (fun r hr hne => ?_) hk
    by_cases hk' : r ∈ ks
    · rw [ite_eq_left_iff.2 (fun h => absurd hk' h)]
      by_cases hg : r = gp
      · subst hg; exact absurd hr hgprs
      · exact (hR r hk' hg).symm
    · rw [ite_eq_right_iff.2 (fun h => absurd h hk')]
      exact hRo r hr hne hk'

/-- A fuel bound uniform over every 64-bit value, from one bound per value
(a finite supremum; the bounds are monotone). -/
theorem fuel_unif {P : Nat → BitVec 64 → Prop} (hmono : ∀ n n' v, n ≤ n' → P n v → P n' v)
    (h : ∀ v, ∃ n, P n v) : ∃ n, ∀ v, P n v := by
  have key : ∀ k, ∃ n, ∀ v : BitVec 64, v.toNat < k → P n v := by
    intro k
    induction k with
    | zero => exact ⟨0, fun v hv => absurd hv (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨n1, h1⟩ := ih
      obtain ⟨n2, h2⟩ := h (BitVec.ofNat 64 k)
      refine ⟨max n1 n2, fun v hv => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with hv | hv
      · exact hmono _ _ _ (Nat.le_max_left _ _) (h1 v hv)
      · have e : v = BitVec.ofNat 64 k := BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_ofNat, ← hv, Nat.mod_eq_of_lt v.isLt])
        subst e
        exact hmono _ _ _ (Nat.le_max_right _ _) h2
  obtain ⟨n, hn⟩ := key (2 ^ 64)
  exact ⟨n, fun v => hn v v.isLt⟩

/-- **A load from bytes the run does not own** (`swp_havoc`). The segment
writes no memory and changes the owned registers `ks` as the reflection
says; the destination `rd` receives whatever the bytes `A` hold in the
actual state, so the continuation must hold for every value. The loaded
byte lists are a function `ldsOf` of the memory's reads on `A`. -/
theorem swp_havocD {pc0 pc1 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (bs : List BBlock) (ks : List Nat) (rd : Nat) (A : List Nat)
    (ldsOf : (Nat → BitVec 8) → List (List (BitVec 8))) (k : Nat)
    (hdep : ∀ f g : Nat → BitVec 8, (∀ a ∈ A, f a = g a) → ldsOf f = ldsOf g)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 ks bs)
    (hkeys : KeysOK ks) (hwr : ∀ x ∈ wrChain bs, x ∈ ks)
    (hcover : ∀ lds a, OutL (segOut bs (pinsOf ks R) lds).log a)
    (hlive : ∀ p ∈ T, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded T m → DataReads D m →
      ChainFacts m m (pinsOf ks R) (ldsOf (imgM m)) bs)
    (hPC : VsaIris.PC ∈ rs) (hrd : rd ∈ ks)
    (hks : ∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC))
    (hgp : ∀ lds, gp ∈ ks → finReg bs (pinsOf ks R) lds gp = gpV) (hgprs : gp ∉ rs)
    (hpc : ∀ lds, evalBlocksPC pc0 (SegEvalState.init (pinsOf ks R) lds) bs = pc1)
    (hR : ∀ lds, ∀ x ∈ ks, x ≠ gp → x ≠ rd → finReg bs (pinsOf ks R) lds x = R x)
    (hk : ∀ v, SWP live (T ++ D) rs S Q pc1 (upd R rd v) Mt) :
    SWP live (T ++ D) rs S Q pc0 R Mt := by
  have hK := keysG_pinsOf R ks
  obtain ⟨n, hn⟩ := fuel_unif (P := fun n v => ∀ rv mv, Matches rs S pc1 (upd R rd v) Mt rv mv →
      LocalRun (vsaModel live) roR (T ++ D) rs S Q n rv mv)
    (fun _ _ _ hle h rv mv hm => LocalRun.fuel_mono hle (h rv mv hm)) hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨k, fun σ hok hro hrs hS => ?_⟩⟩
  let f : Nat → BitVec 8 := imgM σ.σ.mem
  let X : List (Nat × BitVec 8) := A.map fun a => (a, f a)
  have hseg : SegFrom (vsaModel live) roR ((T ++ D) ++ X) rs S k rv mv
      (LocalRun (vsaModel live) roR (T ++ D) rs S Q n) := by
    refine segFrom_of_runFact (seg_runFact live bs (pinsOf ks R) (ldsOf f) pc0
      (textMRof ((T ++ D) ++ X)) [] k hlen (by rw [hK]; exact hwf) (by rw [hK]; exact hkeys)
      (fun x hx => by rw [hK]; exact hwr x hx) (fun a _ => hcover _ a) ?_) ?_ ?_ ?_ ?_ ?_
    · intro c hok' hfoot
      obtain ⟨_, hMR, _, _⟩ := hfoot
      have hin : ∀ q ∈ (T ++ D) ++ X, (c.σ.mem[q.1]?).getD 0 = q.2 := fun q hq =>
        hMR (q.1, DFrac.discard, q.2) (List.mem_map_of_mem
          (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hq)
      have hT : TextLoaded T c.σ.mem := by
        have h := code_present hok' (textMRof T)
          (fun q hq => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            exact hin p (List.mem_append_left _ (List.mem_append_left _ hp)))
          (fun q hq => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            exact hlive p hp)
        intro p hp
        exact h _ (List.mem_map_of_mem (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hp)
      have hD : DataReads D c.σ.mem := fun p hp =>
        hin p (List.mem_append_left _ (List.mem_append_right _ hp))
      have hA : ∀ a ∈ A, imgM c.σ.mem a = f a := fun a ha =>
        hin (a, f a) (List.mem_append_right _ (List.mem_map_of_mem (f := fun a => (a, f a)) ha))
      have := hfacts c.σ.mem hT hD
      rwa [hdep _ _ hA] at this
    · intro p hp; cases hp
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact .inl hq
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .inl ⟨hPC, hm.pc⟩
      · obtain ⟨⟨x, w⟩, hx, rfl⟩ := List.mem_map.mp hp
        obtain ⟨x', hx', e⟩ := List.mem_map.mp hx
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        by_cases hg : x' = gp
        · subst hg
          exact .inr ⟨by simp [roR], by simpa using hgp _ hx'⟩
        · rcases hks x' hx' with h | ⟨h1, h2⟩
          · exact absurd h hg
          · exact .inl ⟨h1, by simp [hg, hm.regs x' h1 h2]⟩
    · intro p hp; cases hp
    · intro rv' mv' h1 h2 _ h4
      refine hn (finReg bs (pinsOf ks R) (ldsOf f) rd) rv' mv' ⟨?_, fun r hr hne => ?_, fun a ha => ?_⟩
      · exact (h1 _ List.mem_cons_self).trans (hpc _)
      · by_cases hkr : r ∈ ks
        · have hr1 := h1 (r, if r = gp then gpV else R r, finReg bs (pinsOf ks R) (ldsOf f) r)
            (List.mem_cons_of_mem _ (List.mem_map_of_mem
              (f := fun p => (p.1, p.2, finReg bs (pinsOf ks R) (ldsOf f) p.1))
              (List.mem_map_of_mem (f := fun k => (k, if k = gp then gpV else R k)) hkr)))
          refine hr1.trans ?_
          have hng : r ≠ gp := fun e => hgprs (e ▸ hr)
          by_cases hrr : r = rd
          · subst hrr; rw [upd_same]
          · rw [upd_other _ _ hrr, hR _ r hkr hng hrr]
        · have hrr : r ≠ rd := fun e => hkr (e ▸ hrd)
          rw [upd_other _ _ hrr]
          refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
          rcases List.mem_cons.mp hp with rfl | hp
          · exact fun e => hne e.symm
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
            exact fun e => hkr (e ▸ hx)
      · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]
  refine hseg σ hok ⟨hro.1, fun p hp => ?_⟩ hrs hS
  rcases List.mem_append.mp hp with hp | hp
  · exact hro.2 p hp
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    rfl

end SWPD

end VsaIris.Sym

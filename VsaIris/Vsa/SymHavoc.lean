import VsaIris.Vsa.SymData

/-!
# Loads of partly known bytes

`swp_havocD` (`SymData.lean`) loads bytes the run knows nothing about. A word
load past a string's NUL (`strlen`'s word loop on a `strAt` string: the
string's bytes are persistent data, the at most seven bytes after the NUL
belong to someone else, `StrWin` only makes them RAM) reads bytes of both
kinds. `swp_havocP` keeps what is known: the loaded value is that of SOME
memory image agreeing with the data view and the owned bytes.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section SWPD

variable {live : Nat → Prop} {T D : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **A load of partly known bytes** (`swp_havocD`, refined). The bytes `A`
may mix data bytes, owned bytes and bytes the run neither owns nor reads
persistently (a word load past a string's NUL). The destination receives the
loaded value of SOME memory image `f` that agrees with the data view and the
owned bytes; the continuation must hold for each such value. -/
theorem swp_havocP {pc0 pc1 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
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
    (hk : ∀ v, (∃ f : Nat → BitVec 8, (∀ p ∈ D, f p.1 = p.2) ∧ (∀ a, S a → f a = imgM Mt a) ∧
      v = finReg bs (pinsOf ks R) (ldsOf f) rd) → SWP live (T ++ D) rs S Q pc1 (upd R rd v) Mt) :
    SWP live (T ++ D) rs S Q pc0 R Mt := by
  have hK := keysG_pinsOf R ks
  obtain ⟨n, hn⟩ := fuel_unif (P := fun n v => (∃ f : Nat → BitVec 8, (∀ p ∈ D, f p.1 = p.2) ∧
      (∀ a, S a → f a = imgM Mt a) ∧ v = finReg bs (pinsOf ks R) (ldsOf f) rd) →
      ∀ rv mv, Matches rs S pc1 (upd R rd v) Mt rv mv →
      LocalRun (vsaModel live) roR (T ++ D) rs S Q n rv mv)
    (fun _ _ _ hle h hc rv mv hm => LocalRun.fuel_mono hle (h hc rv mv hm)) (fun v => by
      by_cases hc : ∃ f : Nat → BitVec 8, (∀ p ∈ D, f p.1 = p.2) ∧ (∀ a, S a → f a = imgM Mt a) ∧
          v = finReg bs (pinsOf ks R) (ldsOf f) rd
      · obtain ⟨n, hn⟩ := hk v hc
        exact ⟨n, fun _ => hn⟩
      · exact ⟨0, fun h => absurd h hc⟩)
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
      refine hn (finReg bs (pinsOf ks R) (ldsOf f) rd)
        ⟨f, fun p hp => (hro.2 p (List.mem_append_right _ hp)), fun a ha => (hS a ha).trans (hm.img a ha),
          rfl⟩ rv' mv' ⟨?_, fun r hr hne => ?_, fun a ha => ?_⟩
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

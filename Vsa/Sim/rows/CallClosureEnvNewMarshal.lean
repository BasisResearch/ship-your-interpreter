import Vsa.Sim.AllocClosure
import Vsa.Sim.rows.CallClosureRow

/-!
# `CallClosureEnvNewMarshal` — the `StoreRepr`–`allocFrame` marshalling (wave 38)

Task Wave-38, residual span (b): the `φf'`-binding core of the `hEnvNewToFold`
bridge (`rows/CallClosureSplice.lean`, `callClosureEntrySplice`).  `env_new`
returns a fresh 32-byte `Env` at `p` representing the EMPTY frame
`⟨some cd.env, []⟩` (`env_new_post`'s `FrameRepr`); on the spec side `a_4` says
`st.store.allocFrame (some cd.env) = (store', frame)`.  This file lands:

* `allocFrame_inv` — the `a_4` inversion (`store'` is the push, `frame` is the
  old size);
* `pushFrameMap`/`pushFrameMap_extends` — the canonical one-point extension of
  the frame map at the fresh spec address, with its `PhiExtends` witness (this
  is the `φf'` the entry splice ∃-binds);
* `storeRepr_allocFrame` — the FRAME-side sibling of
  `AllocClosure.storeRepr_pushClosure` (the model, mirrored field-for-field):
  a store represented under the extended map, plus the fresh frame's
  `FrameRepr`/arena/alignment/freshness facts, represents the pushed store.

As in the model, `hOld` is stated at the EXTENDED map `φf'` — the caller
rewrites its `StoreRepr … φf` through `PhiExtends` (only addresses
`< s.frames.size` occur; the `EnvGetMarshal`/`GrowEnvEntry` discipline), and
gets freshness from malloc's `ExtDisjoint` against the old frame images.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open Vsa Vsa.While
open Vsa.RuntimeRepr
open Vsa.MemRepr

namespace Vsa.Sim

/-- **`a_4` inversion**: `allocFrame` returns the pushed store and the old
frame count. -/
theorem allocFrame_inv {s s' : Store} {par : Option Addr} {fr : Addr}
    (h : s.allocFrame par = (s', fr)) :
    s' = { s with frames := s.frames.push ⟨par, []⟩ } ∧ fr = s.frames.size := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact ⟨h1.symm, h2.symm⟩

/-- The canonical one-point extension of the frame map: the fresh spec frame
`n` (= the pre-store's `frames.size`) maps to the fresh machine `Env` at `p`;
everything else is `φf`.  This is the `φf'` the entry splice ∃-binds
(`hEnvNewToFold`). -/
def pushFrameMap (φf : Addr → Nat) (n p : Nat) : Addr → Nat :=
  fun a => if a = n then p else φf a

theorem pushFrameMap_extends (φf : Addr → Nat) (n p : Nat) :
    PhiExtends φf (pushFrameMap φf n p) n := by
  intro a ha
  unfold pushFrameMap
  rw [if_neg (Nat.ne_of_lt ha)]

/-- `pushFrameMap` at the fresh address is `p`. -/
theorem pushFrameMap_fresh (φf : Addr → Nat) (n p : Nat) :
    pushFrameMap φf n p n = p := by
  unfold pushFrameMap; rw [if_pos rfl]

/-- **The frame-side push marshalling** — the `allocFrame` sibling of
`storeRepr_pushClosure` (`AllocClosure`, the model), field-for-field:

* `hOld` — the pre-store represented under the EXTENDED map `φf'` (the caller
  rewrites its `φf`-`StoreRepr` through `PhiExtends φf φf' s.frames.size`);
* `hp` — the fresh frame's machine image `φf' s.frames.size = p`;
* `hrepr` — `FrameRepr m N φf' φc p ⟨parent, []⟩` (`env_new_post`'s fresh-Env
  representation, φ-transported by the caller);
* `harena`/`halign` — the 32-byte `Env` block is in-arena and 8-aligned
  (`env_new_post` gives 16-alignment, weaken);
* `hpfresh` — `p` differs from every old frame image (from malloc's
  `ExtDisjoint` freshness against the old frames).

The closures side carries over verbatim (`allocFrame` grows only frames). -/
theorem storeRepr_allocFrame
    {m : Mem} {N : NativeAddrs} {A : Arena} {φf' φc : Addr → Nat} {s : Store}
    {parent : Option Addr} {p : Nat}
    (hOld : StoreRepr m N A φf' φc s)
    (hp : φf' s.frames.size = p)
    (hrepr : FrameRepr m N φf' φc p ⟨parent, []⟩)
    (harena : A.contains p 32) (halign : p % 8 = 0)
    (hpfresh : ∀ fa, fa < s.frames.size → φf' fa ≠ p) :
    StoreRepr m N A φf' φc (s.allocFrame parent).1 where
  frames fa hfa := by
    have hfa' : fa < (s.frames.push ⟨parent, []⟩).size := hfa
    rw [Array.size_push] at hfa'
    rcases Nat.lt_or_ge fa s.frames.size with hlt | hge
    · -- old frame: carries over (already indexed at φf')
      have hval := hOld.frames fa hlt
      have heq : (s.allocFrame parent).1.frames[fa]'hfa = s.frames[fa] :=
        Array.getElem_push_lt (h := hlt)
      rw [heq]; exact hval
    · -- the fresh frame at index s.frames.size
      have hfe : fa = s.frames.size := by omega
      subst hfe
      have heq : (s.allocFrame parent).1.frames[s.frames.size]'hfa
          = ⟨parent, []⟩ := Array.getElem_push_eq
      rw [heq, hp]; exact hrepr
  closures ca hca := hOld.closures ca hca
  φf_inj a b ha hb h := by
    have ha' : a < (s.frames.push ⟨parent, []⟩).size := ha
    have hb' : b < (s.frames.push ⟨parent, []⟩).size := hb
    rw [Array.size_push] at ha' hb'
    rcases Nat.lt_or_ge a s.frames.size with hla | hga <;>
      rcases Nat.lt_or_ge b s.frames.size with hlb | hgb
    · exact hOld.φf_inj a b hla hlb h
    · have hbe : b = s.frames.size := by omega
      subst hbe
      exact absurd (hp ▸ h) (hpfresh a hla)
    · have hae : a = s.frames.size := by omega
      subst hae
      exact absurd (hp ▸ h.symm) (hpfresh b hlb)
    · omega
  φc_inj a b ha hb h := hOld.φc_inj a b ha hb h
  frames_arena fa hfa := by
    have hfa' : fa < (s.frames.push ⟨parent, []⟩).size := hfa
    rw [Array.size_push] at hfa'
    rcases Nat.lt_or_ge fa s.frames.size with hlt | hge
    · exact hOld.frames_arena fa hlt
    · have hfe : fa = s.frames.size := by omega
      subst hfe
      rw [hp]; exact ⟨harena, halign⟩
  closures_arena ca hca := hOld.closures_arena ca hca

#print axioms allocFrame_inv
#print axioms pushFrameMap_extends
#print axioms pushFrameMap_fresh
#print axioms storeRepr_allocFrame

end Vsa.Sim

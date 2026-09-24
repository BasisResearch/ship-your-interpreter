import VsaIris.Interp.CallNativeSeg
import VsaIris.Interp.CallPrefixP

/-!
# The closure call: its resources (lane E4)

`interp.c:180-208` (`call_value`'s closure path, inlined in `eval_expr`):
read the closure object (`fn_expr`, `env`), the `EX_FN` node (`paramc`,
`params`, `body`), bump `in->call_depth`, `env_new(cl->env)`, bind the
parameters (`env_define`), run the body (G's closure loop), drop the depth,
and return `null` or the returned value.

This file: what the path reads besides the frame.

* `CloRes s ca p` (persistent): the closure `ca` at `p`: its store entry
  `cd`, its 16 bytes read-only with their read geometry, the `EX_FN` node's
  view (`ExprReprWithin`, `ReadOK`, `SharedWin`), and its environment's
  binding. `CloSupply N` (a NAMED premise, `PROOF_CLOSURE_PLAN.md` lane E4):
  every closure the store owns has it. It subsumes `DispSupply`
  (`dispSupply_of_cloSupply`).
* `roOwn_roImg`: a data view of a read-only image (the closure object).
* `world_store`, `world_depth`: the store and the depth word out of the
  world, and back.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

section Defs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The pure facts of a closure's resources. -/
structure CloFactsE (s : Store) (ca p : Nat) (cd : ClosureData) (q e : Nat) (img : Nat → BitVec 8)
    (P : Nat → Prop) (m : Mem) : Prop where
  lookup : s.closures[ca]? = some cd
  fn : imgLE img p 8 = q
  env : imgLE img (p + 8) 8 = e
  objOK : ∀ k, InExt (p, 16) k → ReadOK k
  repr : ExprReprWithin m P q (.fn cd.name cd.params cd.body)
  geo : ∀ k, P k → ReadOK k
  win : SharedWin P

/-- **A closure's resources** (persistent): the object's bytes, the `EX_FN`
node's view, the environment's binding. -/
def CloRes (s : Store) (ca p : Nat) : IProp GF :=
  iprop(∃ (cd : ClosureData) (q e : Nat) (img : Nat → BitVec 8) (P : Nat → Prop) (m : Mem),
    ⌜CloFactsE s ca p cd q e img P m⌝ ∗ roImg (InExt (p, 16)) img ∗ roOn P m ∗ frameAt cd.env e)

instance (s : Store) (ca p : Nat) : Persistent (CloRes (GF := GF) s ca p) := by
  unfold CloRes; infer_instance

/-- **The closures' read geometry, from the store** (a NAMED premise;
`closOwn` carries the bytes but not their `ReadOK`/`SharedWin` geometry, H2's
finding; supplier: a geometry field on `closOwn`, from the `EX_FN` arm). -/
def CloSupply (N : NativeAddrs) : Prop :=
  ∀ (s : Store) (B : List (Nat × Nat)) (ca p : Nat),
    storeRepr (GF := GF) N s B ∗ closAt ca p ⊢ storeRepr N s B ∗ CloRes s ca p

theorem dispSupply_of_cloSupply {N : NativeAddrs} (h : CloSupply (GF := GF) N) :
    DispSupply (GF := GF) N := by
  intro s B ca p
  iintro ⟨Hs, #Hc⟩
  ihave ⟨Hs, #Hr⟩ := h s B ca p $$ [Hs Hc]
  · iframe Hs Hc
  iframe Hs
  unfold CloRes
  icases Hr with ⟨%cd, %q, %e, %img, %P, %m, %hf, #Himg, #Hro, -⟩
  unfold dispRes
  iexists cd, p, q, img, P, m
  iframe Hc Himg Hro
  ipureintro
  exact ⟨hf.lookup, hf.fn, hf.objOK, hf.repr, hf.geo, hf.win⟩

end Defs

section Views

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **A data view of a read-only image** (the closure object): a memory
agreeing with the image on the range. -/
theorem roOwn_roImg {img : Nat → BitVec 8} {p n : Nat} :
    codeRes (GF := GF) ∗ roImg (InExt (p, n)) img ⊢
      ∃ Dt : Mem, roOwn roR (interpText ++ dataOf Dt (accAddrs p n)) ∗
        ⌜∀ k, p ≤ k → k < p + n → imgM Dt k = img k⌝ := by
  iintro ⟨#Hc, #H1⟩
  obtain ⟨Dt, hDt⟩ := exists_mem_img img (accAddrs p n)
  have hc : ∀ k, p ≤ k → k < p + n → imgM Dt k = img k := fun k h1 h2 =>
    hDt k (mem_accAddrs_iff.2 ⟨h1, h2⟩)
  iexists Dt
  isplitl
  · unfold codeRes roOwn at *
    icases Hc with ⟨#Hgp, #Htx⟩
    iframe Hgp
    iapply (sepL_append _ _ _).2
    iframe Htx
    unfold dataOf
    rw [sepL_map]
    iapply sepL_of_persistent (roImg (InExt (p, n)) img) _ _ (fun k hk => by
      obtain ⟨h1, h2⟩ := mem_accAddrs_iff.1 hk
      rw [hc k h1 h2]
      unfold roImg
      iintro #H
      iapply H $$ %k %(show InExt (p, n) k by simp [InExt]; omega)) $$ H1
  · ipureintro; exact hc

end Views

section World

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **The store out of the world**, and back (the heap, console, newlib's
data and the context stay in the closer). -/
theorem world_store (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (ρ : Regime)
    (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢
      ∃ B, storeRepr N st.store B ∗ (storeRepr N st.store B -∗ world N L Room inp ρ st d) := by
  unfold world worldE
  iintro ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hb⟩
  iexists B
  iframe Hs
  iintro Hs
  iexists H, B
  iframe Hh Hs Hc Hio Hi
  isplitr
  · ipureintro; exact hB
  · iexact Hb

/-- **The depth word out of the world**, and back at any depth. -/
theorem world_depth (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (ρ : Regime)
    (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢
      ∃ img : Nat → BitVec 8, ownImg (InExt (inp + interpDepthOff, 4)) img ∗
        ⌜imgLE img (inp + interpDepthOff) 4 = d⌝ ∗
        (∀ (d' : Nat) (img' : Nat → BitVec 8), ownImg (InExt (inp + interpDepthOff, 4)) img' -∗
          ⌜imgLE img' (inp + interpDepthOff) 4 = d'⌝ -∗ world N L Room inp ρ st d') := by
  unfold world worldE interpCtxE interpCoreE wordAt
  iintro ⟨%H, %B, Hh, Hs, Hc, Hio, ⟨⟨%g, Hg, Hfa, ⟨%img, Hd, %hd⟩, Hpad, He⟩, Hjb⟩, %hB, #Hb⟩
  iexists img
  iframe Hd
  isplitl []
  · ipureintro; exact hd
  iintro %d' %img' Hd %hd'
  iexists H, B
  iframe Hh Hs Hc Hio Hjb
  isplitl [Hg Hfa Hd Hpad He]
  · iexists g
    iframe Hg Hfa Hpad He
    iexists img'
    iframe Hd
    ipureintro; exact hd'
  · isplitr
    · ipureintro; exact hB
    · iexact Hb

end World

end VsaIris.Interp

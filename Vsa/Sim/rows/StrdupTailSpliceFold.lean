import Vsa.Sim.SpliceFold
import Vsa.Sim.CallFrameMeta
import Vsa.Sim.rows.StringifyStrdupTail
import Vsa.Sim.rows.StrdupMallocArgGen

/-!
# `StrdupTailSpliceFold` — the strdup-tail splice RE-SEATED through `spliceFold`

PILOT for the CallSpec layer (wave 36).  `stringifyStrdupTailContract`
(`rows/StringifyStrdupTail.lean`, the landed hand route — UNTOUCHED, it is the
regression guard) composes the shared strdup tail
`strlen ≫ malloc ≫ memcpy ≫ epilogue` through THREE bespoke per-callee splice
theorems (`envDefStrlenSplice` / `envDefMallocSplice` /
`envDefMemcpyFramedSplice`, `EnvDefCompose.lean` — ~120 statement lines that
exist ONLY to nest `callSeg` around one particular callee each).

`stringifyStrdupTailContract_viaSpliceFold` below is the SAME theorem — same
premises, same conclusion — proved by ONE `spliceFold` over the generic
`SpliceChain`: the per-callee splice zoo is not needed at all.  Any other call
sequence (concat C-block, `env_define` append/grow, `env_new`) gets its
composition for free from the same fold, with NO new per-callee theorems.

Also landed here: the red-zone metatheorem FIRING on the real strdup
malloc-staging log — `strdupMallocSpill_logInRZ` (the log containment, one
small proof) and `strdupAInvStableSpill_of_rz` (the OLD `hAInvStableSpill`
premise shape of `rows/StrdupTailContractClose.lean` derived from the ONE
canonical `AInvStableOn` premise — the per-window stability family, dead).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.Alloc
open Vsa.RuntimeRepr
open Vsa.MemRepr

namespace Vsa.Sim

/-! ## §1. The re-seat: the whole tail composition as ONE `spliceFold` -/

/-- **`stringifyStrdupTailContract` via `spliceFold`.**  Statement identical to
the landed hand route (`rows/StringifyStrdupTail.lean:130`); the proof replaces
the three bespoke per-callee splice theorems with one generic fold —
`strlen`-hop ≫ `malloc`-hop ≫ `memcpy`-hop ≫ epilogue tail. -/
theorem stringifyStrdupTailContract_viaSpliceFold
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {P : Config → Prop}
    (M : MallocContract A SL gpv headroom maxReq)
    (gm : (R : Register) → Option (RegisterType R))
    (str : String) (rRet : BitVec 64)
    -- strlen call data
    (bufPtr rStrlen : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    -- malloc call data
    (exts : List (Nat × Nat)) (nMalloc : Nat) (spM rM : BitVec 64)
    (mMalloc : Std.ExtHashMap Nat (BitVec 8)) (hnM : nMalloc ≤ maxReq)
    -- memcpy call data (dispatch ghost = the reseated ghost; byte route)
    (rMemcpy dst src : BitVec 64) (nMemcpy : Nat)
    (mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halignC : rMemcpy.toNat % 4 = 0)
    (extsC : List (Nat × Nat)) (spC : BitVec 64)
    (hrouteCbyte : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ nMemcpy < 8)
    (hAInvStableFootC : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < dst.toNat ∨ dst.toNat + nMemcpy ≤ a) → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa extsC → M.AInv σb extsC)
    -- strlen preserves the carried frame (its missing preservation clause, named)
    (strlenFramed : Triple
      (fun c => strlen_pre bufPtr rStrlen str m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c)
      (fun c => strlen_post rStrlen str m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c))
    -- the four machine bridges (identical to the hand route's premises)
    (bridgeStrlenPre : Triple P
      (fun c => strlen_pre bufPtr rStrlen str m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c))
    (bridgeMallocPre : Triple
      (fun c => strlen_post rStrlen str m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 nMalloc) ∧
        c.σ.regs.get? Register.x1 = some rM ∧ rM.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some spM ∧ StackOK SL spM headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        M.AInv c.σ exts ∧ c.σ.mem = mMalloc))
    (bridgeMemcpyPre : Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some rM ∧
        c.σ.regs.get? Register.x2 = some spM ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ exts) ∨
         (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
           p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p nMalloc ∧
           (∀ e ∈ exts, ExtDisjoint (p, nMalloc) e) ∧
           M.AInv c.σ ((p, nMalloc) :: exts))) ∧
        (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < spM.toNat) →
          c.σ.mem[a]? = mMalloc[a]?))
      (fun c => PreDispatch (ghostReseatS0 gm dst) rMemcpy dst src nMemcpy mMemcpy bs c ∧
        EnvDefFrame SL gpv headroom M.AInv extsC spC (ghostReseatS0 gm dst) c))
    (bridgeEpilogue : Triple
      (fun c => (∃ g', memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs c) ∧
        EnvDefFrame SL gpv headroom M.AInv extsC spC (ghostReseatS0 gm dst) c)
      (StrdupTailExit rRet str)) :
    Triple P (StrdupTailExit rRet str) :=
  -- ONE generic fold; hop callees are the real contracts, verbatim.
  spliceFold
    (.step bridgeStrlenPre strlenFramed
      (.step bridgeMallocPre (M.spec gm exts nMalloc spM rM mMalloc hnM)
        (.step bridgeMemcpyPre
          (envDefMemcpyFramed SL gpv headroom M.AInv extsC spC (ghostReseatS0 gm dst)
            rMemcpy dst src nMemcpy mMemcpy bs halignC hrouteCbyte hAInvStableFootC)
          (.tail bridgeEpilogue))))

#print axioms stringifyStrdupTailContract_viaSpliceFold

/-! ## §2. The red-zone metatheorem firing on the real strdup staging log

The malloc-staging seg (`addi a2,a0,1 ; mv a0,a2 ; sd a2,8(sp)`,
`strdupMallocArgSeg`) spills exactly one doubleword at `spM+8`.  Its red zone
is `[spM+8, spM+16)`. -/

/-- The strdup malloc-staging spill red zone. -/
def strdupSpillRZ (spM : BitVec 64) : RedZone :=
  ⟨(spM + 8#64).toNat, (spM + 8#64).toNat + 8⟩

/-- **Log containment, one small proof**: the malloc-staging seg's reflected
write-log lands inside its red zone.  (The `sd a2,8(sp)` is the only entry;
the reflected address is `spM + sign_extend 8`.) -/
theorem strdupMallocSpill_logInRZ (lenW spM : BitVec 64) :
    LogInRZ (strdupSpillRZ spM)
      (evalBlocks strdupMallocArgSeg
        (SegEvalState.init (strdupMallocArgL lenW spM) [])).log := by
  have hlog : (evalBlocks strdupMallocArgSeg
      (SegEvalState.init (strdupMallocArgL lenW spM) [])).log
      = [((spM + sign_extend (m := 64) (0x008#12)).toNat, 8,
          lenW + sign_extend (m := 64) (0x001#12))] := by rfl
  rw [hlog]
  refine ⟨?_, trivial⟩
  have hsext8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext8]
  show (strdupSpillRZ spM).lo ≤ (spM + 8#64).toNat ∧
    (spM + 8#64).toNat + 8 ≤ (strdupSpillRZ spM).hi
  have hlo : (strdupSpillRZ spM).lo = (spM + 8#64).toNat := rfl
  have hhi : (strdupSpillRZ spM).hi = (spM + 8#64).toNat + 8 := rfl
  omega

/-- **The old per-window stability premise, DERIVED.**  The exact
`hAInvStableSpill` shape `stringifyStrdupTailContract_closed`
(`rows/StrdupTailContractClose.lean`) threads per-splice is a corollary of the
ONE canonical `AInvStableOn` premise at the spill red zone — the bespoke
window-stability family is replaced by one named shape + `mono`. -/
theorem strdupAInvStableSpill_of_rz
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (spM : BitVec 64)
    (h : AInvStableOn AInv exts (strdupSpillRZ spM).foot) :
    ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < (spM + 8#64).toNat ∨ (spM + 8#64).toNat + 8 ≤ a) →
        σa.mem[a]? = σb.mem[a]?) →
      AInv σa exts → AInv σb exts := by
  intro σa σb hgp hmem
  refine h σa σb hgp ?_
  intro a ha
  refine hmem a ?_
  have ha' : ¬ ((strdupSpillRZ spM).lo ≤ a ∧ a < (strdupSpillRZ spM).hi) := ha
  have hlo : (strdupSpillRZ spM).lo = (spM + 8#64).toNat := rfl
  have hhi : (strdupSpillRZ spM).hi = (spM + 8#64).toNat + 8 := rfl
  omega

#print axioms strdupMallocSpill_logInRZ
#print axioms strdupAInvStableSpill_of_rz

end Vsa.Sim

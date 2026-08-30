import Vsa.Sim.EvalSimCommon

/-!
# Layer 4 — M4 RECURSIVE-case common machinery: the IH-application glue

The leaf `EvalE` cases (`int`/`str`/`bool`/`null`/`var`) close their arms with
`armTail_v`: a `jal <value_*>` whose callee post is a *leaf* `value_*` spec.
The recursive cases (`neg`/`not`/`assign`/`binary`/`logical`/`call`) instead
contain `jal eval_expr` — the callee is `eval_expr` itself, and its behavior is
the **induction hypothesis** of the Layer-4 mutual recursion: a
`Triple (EvalEntry …) (EvalExit …)` for the sub-derivation. This file provides
the `armTail_v` analogue for that shape:

* **`MemExtends`** — presence-monotonicity of memory. The post-call code of a
  recursive arm re-reads the whole 24-byte sub-result buffer (`ld a3,144(sp)`
  reads bytes `[subsret, subsret+8)`, `ld a4,160(sp)` reads
  `[subsret+16, subsret+24)`), but `ValueRepr … (.int n)` pins only the kind
  word and the payload — bytes 4–7 and 16–23 are unconstrained. The machine
  `ld` still needs them *present*. `EvalExit` says nothing about presence, so
  the recursive motive must be stated against the widened exit below.
* **`EvalExitD`** — `EvalExit` plus (a) `MemExtends m0 mem` and (b) an
  exit-side `StoreRepr`-survival clause over the whole stack region
  `[SL.lo, SL.hi)` (the caller's *remaining* writes — its own sret write, its
  own spill traffic — all land in the stack region; the entry-side
  `store_survives` is for the *entry* store `st.store` at the *entry* maps and
  is useless for `st'.store` at the extended maps).
* **`EvalIH`** — the recursive-case motive shape: the ∀-closed
  `Triple (EvalEntry …) (EvalExitD …)` for a sub-derivation. This is
  `InductionScaffold.motive_EvalE` with `EvalExit` replaced by `EvalExitD`;
  the leaf minor premises must be re-landed at this exit (mechanical: their
  memory deltas are `writeMap4/8` chains, which preserve presence, and their
  store survival comes from the entry clause — RESIDUAL, tracked in
  `memory/m4-recursive-cases.md`).
* **`SubEvalReturn`** — the machine state a recursive arm holds right after
  its `jal eval_expr` returns: PC at the link, sub-result represented at
  `subsret`, `st'.store` re-represented (+ survival), the four spill slots
  intact, `eval_expr`'s code still loaded, callee-saved registers restored to
  the call-point frame `gpre`, memory framed to the pre-call memory `mcall`
  outside (sub-stack-window ∪ arena ∪ subsret), presence-extended.
* **`armTail_rec`** — THE GLUE: `jal eval_expr` (per-arm site hypothesis) ≫
  IH ⇒ `SubEvalReturn`. It builds the sub-call's `EvalEntry` from the arm
  state (choosing the sub-ghosts: `g_sub` := the post-`jal` register file,
  `sp_sub := sp - 1088`, `m0_sub := mcall`), applies the IH, and repackages
  `EvalExitD` into `SubEvalReturn` (spill-slot survival via the exit
  `memFrame` + arena/stack disjointness, code survival via
  `loaded_eval_expr_agreeP`, frame composition across the `jal`).

Geometry notes (all recorded as explicit hypotheses):
* the sub-call needs its own 2176-byte `StackOK` headroom below `sp - 1088`,
  so a recursive arm's entry must carry `SL.lo + 3264 ≤ sp` — ONE extra
  1088-byte frame per recursion level. The fully general induction needs
  depth-indexed headroom (`SL.lo + 1088 * (depthLeft…) ≤ sp`) — RESIDUAL.
* the arena must be disjoint from the stack region and from `eval_expr`'s
  code (`harenaStk`/`harenaCode`): the sub-call may genuinely allocate
  (arena writes), and the spill slots / code must survive that.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `MemExtends` — presence monotonicity -/

/-- Every address populated in `m0` is still populated in `m`. All real machine
memory deltas are `writeMap4/8` chains (inserts), so every verified walk
preserves this; it is the fact `EvalExit` forgets and recursive callers need
(the post-call `ld`s of the unconstrained sub-result padding bytes). -/
def MemExtends (m0 m : Mem) : Prop :=
  ∀ (a : Nat) (b : BitVec 8), m0[a]? = some b → ∃ b', m[a]? = some b'

theorem MemExtends.refl (m : Mem) : MemExtends m m := fun _ b h => ⟨b, h⟩

/-- A `writeMap8` (an 8-byte insert) preserves presence: nothing is deleted, and
the 8 written bytes are present. -/
theorem memExtends_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8)) :
    MemExtends mem (writeMap8 mem a8 d) := by
  intro k b hk
  by_cases hin : a8 ≤ k ∧ k < a8 + 8
  · obtain ⟨hlo, hhi⟩ := hin
    rcases (show k = a8 ∨ k = a8 + 1 ∨ k = a8 + 2 ∨ k = a8 + 3 ∨ k = a8 + 4 ∨
        k = a8 + 5 ∨ k = a8 + 6 ∨ k = a8 + 7 from by omega)
      with h | h | h | h | h | h | h | h
    · exact ⟨_, by rw [show k = a8 + 0 from by omega]; exact getElem_writeMap8_0 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_1 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_2 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_3 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_4 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_5 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_6 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_7 mem a8 d⟩
  · exact ⟨b, by rw [getElem_writeMap8_disjoint mem a8 k d (by omega)]; exact hk⟩

/-- A `writeMap4` (a 4-byte insert) preserves presence. -/
theorem memExtends_writeMap4 (mem : Mem) (a4 : Nat) (d : BitVec (8 * 4)) :
    MemExtends mem (writeMap4 mem a4 d) := by
  intro k b hk
  by_cases hin : a4 ≤ k ∧ k < a4 + 4
  · obtain ⟨hlo, hhi⟩ := hin
    rcases (show k = a4 ∨ k = a4 + 1 ∨ k = a4 + 2 ∨ k = a4 + 3 from by omega)
      with h | h | h | h
    · exact ⟨_, by rw [show k = a4 + 0 from by omega]; exact getElem_writeMap4_0 mem a4 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap4_1 mem a4 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap4_2 mem a4 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap4_3 mem a4 d⟩
  · exact ⟨b, by rw [getElem_writeMap4_disjoint mem a4 k d (by omega)]; exact hk⟩

theorem MemExtends.trans {m0 m1 m2 : Mem}
    (h1 : MemExtends m0 m1) (h2 : MemExtends m1 m2) : MemExtends m0 m2 := by
  intro a b h
  obtain ⟨b', hb'⟩ := h1 a b h
  exact h2 a b' hb'

/-! ## `EvalExitD` — the presence/survival-widened exit -/

/-- `EvalExit` strengthened with the two clauses every recursive CALLER needs
from its sub-call:
1. presence monotonicity (`MemExtends m0 mem`);
2. an exit-side `StoreRepr` survival clause: the re-represented `st'.store`
   (at ONE coherent extended map pair) tolerates arbitrary further memory
   changes inside the stack region `[SL.lo, SL.hi)` — where all of the
   caller's remaining writes land. Instantiating `m' := c.σ.mem` recovers the
   plain exit `StoreRepr`. -/
def EvalExitD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop :=
  EvalExit g N A SL φf φc nf nc st' v sp r sret m0 c ∧
  MemExtends m0 c.σ.mem ∧
  ∃ φf' φc' : Addr → Nat,
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store

/-! ## `EvalIH` — the recursive-case motive shape -/

/-- The induction hypothesis a recursive `EvalE` case receives for a
sub-derivation `EvalE st d env e st' v`: the ∀-closed simulation Triple at the
widened exit. This is `InductionScaffold.motive_EvalE` with `EvalExit`
upgraded to `EvalExitD` — the shape the real recursor motive must take
(RESIDUAL: re-land the leaf minor premises at `EvalExitD`). -/
def EvalIH (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple
      (EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' v sp r sret m0)

/-! ## `SubEvalReturn` — the post-sub-call machine state -/

/-- What a recursive arm knows at the instruction after its `jal eval_expr`
(link PC `retPC`), for a sub-derivation with post spec state `st'` and value
`vsub` returned into the buffer `subsret`:

* control back at `retPC`, `a0 = subsret`, `sp` still lowered, `s1 = sret`;
* callee-saved registers restored to the call-point frame `gpre`;
* the sub-result `ValueRepr` at `subsret` (extended `φc'`);
* `st'.store` re-represented at ONE coherent extended pair, WITH the
  stack-region survival clause (for the caller's remaining writes);
* console output = `st'.out`;
* the four prologue spill slots of the OUTER frame intact;
* `eval_expr`'s code still loaded;
* memory framed to the pre-call memory `mcall` outside
  (sub-stack-window ∪ arena ∪ subsret-window), presence-extended. -/
def SubEvalReturn
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (vsub : Value)
    (sp r sret subsret retPC : BitVec 64) (v8 v9 v18 : BitVec 64)
    (mcall : Mem)
    (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some retPC ∧
  c.σ.regs.get? Register.x10 = some subsret ∧
  c.σ.regs.get? Register.x1 = some retPC ∧
  c.σ.regs.get? Register.x9 = some sret ∧
  c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  OutRepr c.σ st' ∧
  (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
  (∃ φc' : Addr → Nat, PhiExtends φc φc' nc ∧
    ValueRepr c.σ.mem N φc' subsret.toNat vsub) ∧
  (∃ φf' φc' : Addr → Nat,
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store ∧
    (∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store)) ∧
  Eval_exprLoaded c.σ.mem ∧
  read64 c.σ.mem (sp.toNat - 8) = some r.toNat ∧
  read64 c.σ.mem (sp.toNat - 16) = some v8.toNat ∧
  read64 c.σ.mem (sp.toNat - 24) = some v9.toNat ∧
  read64 c.σ.mem (sp.toNat - 32) = some v18.toNat ∧
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat - 1088) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (subsret.toNat ≤ a ∧ a < subsret.toNat + 24) ∨ c.σ.mem[a]? = mcall[a]?) ∧
  MemExtends mcall c.σ.mem

/-! ## `armTail_rec` — `jal eval_expr` ≫ IH ⇒ `SubEvalReturn`

The recursive-arm analogue of `armTail_v`. From the arm state at the `jal`'s
PC (`callPC`), with the sub-call's arguments already in place
(`a0 = subsret`, `a1 = aIn`, `a2 = aOperand`, `sp` lowered), one `jal` step
lands at `eval_expr`'s entry with link `retPC = callPC + 4`; the sub-call's
`EvalEntry` is assembled from the arm state, the IH is applied, and its
`EvalExitD` is repackaged into `SubEvalReturn`. -/
theorem armTail_rec
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (vsub : Value)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    -- target arithmetic, fixed by the arm (`decide`-able concretely):
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    -- the per-arm `jal eval_expr` site step:
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    -- the induction hypothesis for the sub-derivation:
    (hIH : EvalIH st d env esub st' vsub) :
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        c.σ.regs.get? Register.x10 = some subsret ∧          -- a0 = sub-sret
        c.σ.regs.get? Register.x9 = some sret ∧              -- s1 = outer sret
        c.σ.regs.get? Register.x11 = some aIn ∧              -- a1 = interp*
        c.σ.regs.get? Register.x12 = some aOperand ∧         -- a2 = operand node
        c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧    -- sp lowered
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
        ExprRepr mcall aOperand.toNat esub ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
            mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) ∧
        read64 mcall (sp.toNat - 8) = some r.toNat ∧
        read64 mcall (sp.toNat - 16) = some v8.toNat ∧
        read64 mcall (sp.toNat - 24) = some v9.toNat ∧
        read64 mcall (sp.toNat - 32) = some v18.toNat ∧
        -- operand-node geometry (the sub-call's `aExpr`):
        aOperand.toNat % 8 = 0 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        -- sub-result buffer geometry: inside the lowered frame, below the spill slots:
        subsret.toNat % 8 = 0 ∧
        sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
        -- stack geometry: recursive headroom (one extra frame), 16-alignment:
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        sp.toNat ≤ 0x100000000 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        -- code/table/arena region disjointness:
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo))
      (SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' vsub sp r sret subsret retPC v8 v9 v18 mcall) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, ha0, hs1, hx11, hx12, hsp, ⟨vmi, hmi⟩, hout, houtStr, hmemc,
    hcode, hviCode, hslot, hsubexpr, hstore, hstoreSurv, hframe, ⟨⟨w8, hw8⟩, ⟨w18, hw18⟩⟩,
    hslotRa, hslotS0, hslotS1, hslotS2,
    hopAl, hopLo, hopHi, hopWin, hopStk,
    hssAl, hssLo, hssHi,
    hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin,
    hcodeStk, hviStk, htableStk, harenaStk, harenaCode⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088 : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  -- ============ callPC: jal eval_expr → PC := 0x80003164, x1 := retPC ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    hjalSite c.σ c.tick c.steps vmi hG hpc hmi (hmemc ▸ hcode) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  have hpc1 : σ1.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry) := by
    have := obs_jalT_pc hobs1; rwa [hjaltgt] at this
  have hlink1 : σ1.regs.get? Register.x1 = some retPC := by
    have := obs_jalT_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlink] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some subsret := obs_jalT_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_jalT_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aIn := obs_jalT_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11
  have hx12_1 : σ1.regs.get? Register.x12 = some aOperand := obs_jalT_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_jalT_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hx8_1 : σ1.regs.get? Register.x8 = some w8 := by
    have hc8 : c.σ.regs.get? Register.x8 = some w8 := (hframe Register.x8 (by decide)).trans hw8
    exact obs_jalT_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc8
  have hx18_1 : σ1.regs.get? Register.x18 = some w18 := by
    have hc18 : c.σ.regs.get? Register.x18 = some w18 := (hframe Register.x18 (by decide)).trans hw18
    exact obs_jalT_other hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc18
  obtain ⟨vmi1, hmi1⟩ := obs_jalT_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_jal]; exact hout
  -- ============ the sub-call's EvalEntry at ⟨σ1, i1, steps+1⟩ ============
  have hEntry : EvalEntry (fun R => σ1.regs.get? R) N A SL φf φc st d env esub
      (sp - 1088#64) retPC subsret aIn aOperand mcall ⟨σ1, i1, c.steps + 1⟩ :=
    { good := hG1
      tick := hi1
      pc := hpc1
      a0 := ha0_1
      a1 := hx11_1
      a2 := hx12_1
      ra := hlink1
      ra_align := hretAl
      spReg := hsp_1
      stackOK := ⟨by rw [hspsub]; omega, by rw [hspsub]; omega, by rw [hspsub]; omega⟩
      minstret := ⟨vmi1, hmi1⟩
      mem := hmem1e
      code := by show Eval_exprLoaded σ1.mem; rw [hmem1e]; exact hcode
      expr := by rw [hmem1e]; exact hsubexpr
      store := by rw [hmem1e]; exact hstore
      store_survives := by
        intro m' hag
        refine hstoreSurv m' (fun k hk1 _ => ?_)
        have hk1' : ¬ (SL.lo ≤ k ∧ k < (sp - 1088#64).toNat) := by
          rw [hspsub]; intro ⟨ha, hb⟩; exact hk1 ⟨ha, by omega⟩
        have hk2' : ¬ (subsret.toNat ≤ k ∧ k < subsret.toNat + 24) := by
          intro ⟨ha, hb⟩; exact hk1 ⟨by omega, by omega⟩
        have := hag k hk1' hk2'
        rwa [hmem1e] at this
      out := by
        show Vsa.Machine.output σ1 = st.out
        simp only [Vsa.Machine.output]; rw [hout1]; exact houtStr
      frame := fun _ _ => rfl
      code_stack_disjoint := by
        rcases hcodeStk with h | h
        · left; rw [hspsub]; omega
        · right; exact h
      expr_stack_disjoint := by
        rcases hopStk with h | h
        · left; exact h
        · right; rw [hspsub]; omega
      expr_align := hopAl
      expr_ram := ⟨hopLo, hopHi⟩
      expr_win := hopWin
      sret_align := hssAl
      sret_ram := ⟨by omega, by omega⟩
      sret_win := by omega
      sret_vicode_disjoint := by
        rcases hviStk with h | h
        · right; omega
        · left; omega
      sret_stack_disjoint := by right; rw [hspsub]; omega
      sret_evalcode_disjoint := by
        rcases hcodeStk with h | h
        · left; omega
        · right; omega
      vicode_stack_disjoint := by
        rcases hviStk with h | h
        · left; exact h
        · right; rw [hspsub]; omega
      stack_ram := ⟨hSLlo, hSLhiRam⟩
      stack_win := hSLwin
      value_int_code := by rw [hmem1e]; exact hviCode
      int_slot := by rw [hmem1e]; exact hslot
      table_stack_disjoint := by
        rcases htableStk with h | h
        · left; exact h
        · right; rw [hspsub]; omega
      spill_defined := ⟨⟨w8, hx8_1⟩, ⟨sret, hs1_1⟩, ⟨w18, hx18_1⟩⟩ }
  -- ============ the sub-call (the induction hypothesis) ============
  obtain ⟨c2, hs2, hExit, hpres, φf', φc', hpf', hpc', hsurvSL⟩ :=
    hIH (fun R => σ1.regs.get? R) N A SL φf φc (sp - 1088#64) retPC subsret aIn aOperand mcall
      ⟨σ1, i1, c.steps + 1⟩ hEntry
  -- PC back at the link (ret target of an aligned retPC)
  have hpcRet : c2.σ.regs.get? Register.PC = some retPC := by
    rw [hExit.pc, ret_tgt retPC hretAl]
  -- frame composition: callee-saved regs at c2 = call-point `gpre`
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe2 : ∀ R : Register, AbiPreservedNoise R → c2.σ.regs.get? R = gpre R := by
    intro R hR
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have hx1R : (Register.x1 == R) = false := abi_ne' (by decide) hab
    -- c2 → σ1 (the sub-call restores every AbiPreservedNoise register to g_sub = σ1)
    have f2 : c2.σ.regs.get? R = σ1.regs.get? R := hExit.frame R hR'
    -- σ1 → c (the jal writes only x1/PC/minstret machinery)
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_jal _ _ _ _ _ _ R hmiR hpcR hx1R hnpcR hmiiR)
    rw [f2, f1]; exact hframe R hR'
  -- s1 (x9) back to the outer sret
  have hs1_2 : c2.σ.regs.get? Register.x9 = some sret := by
    rw [hframe2 Register.x9 (by decide)]
    rw [← hframe Register.x9 (by decide)]; exact hs1
  -- memory agreement outside (sub-stack-window ∪ arena ∪ subsret-window)
  have hmemFrame2 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat - 1088) →
      ¬ (A.lo ≤ a ∧ a < A.hi) →
      (subsret.toNat ≤ a ∧ a < subsret.toNat + 24) ∨ c2.σ.mem[a]? = mcall[a]? := by
    intro a h1 h2
    exact hExit.memFrame a (by rw [hspsub]; exact h1) h2
  -- spill slots survive the sub-call (top 32 bytes of the outer frame:
  -- outside the sub window, outside the arena, above subsret+24)
  have hAgTop : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) mcall c2.σ.mem := by
    intro k hk
    have := hmemFrame2 k (by omega) (by rcases harenaStk with h | h <;> omega)
    rcases this with hin | heq
    · exact absurd hin (by omega)
    · exact heq.symm
  have hslotRa2 : read64 c2.σ.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotRa
  have hslotS02 : read64 c2.σ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS0
  have hslotS12 : read64 c2.σ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS1
  have hslotS22 : read64 c2.σ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS2
  -- eval_expr's code survives (code region outside sub-window/arena/subsret)
  have hcode2 : Eval_exprLoaded c2.σ.mem := by
    refine loaded_eval_expr_agreeP mcall c2.σ.mem (fun a ha => ?_) hcode
    have := hmemFrame2 a
      (by rcases hcodeStk with h | h <;> omega)
      (by rcases harenaCode with h | h <;> omega)
    rcases this with hin | heq
    · exact absurd hin (by rcases hcodeStk with h | h <;> omega)
    · exact heq.symm
  -- assemble SubEvalReturn
  refine ⟨c2, (Steps.single hstep1).trans hs2,
    hExit.good, hExit.tick, hpcRet, hExit.a0, hExit.ra, hs1_2, hExit.spReg, hExit.minstret,
    hExit.out, hframe2, hExit.result,
    ⟨φf', φc', hpf', hpc', hsurvSL c2.σ.mem (fun _ _ => rfl), hsurvSL⟩,
    hcode2, hslotRa2, hslotS02, hslotS12, hslotS22, hmemFrame2, hpres⟩

/-! ## `PreEpilogueVD` — the epilogue-entry state widened for the recursive exit

`PreEpilogueV` plus the two `EvalExitD` upgrade clauses ABOUT the epilogue-entry
memory `mpre`: (1) presence monotonicity `MemExtends m0 mpre`, and (2) the
`[SL.lo,SL.hi)`-survival of the (extended-map) `st.store`. The epilogue is
memory-pure, so both transport verbatim to the exit config; `blockD_v_rec` closes
`PreEpilogueVD → EvalExitD`. A recursive arm's block C produces this (it has both
facts internally — the pre-call memory is fully populated and all of its own
writes land in `[SL.lo,SL.hi)`), whereas the leaf block C's only produce the plain
`PreEpilogueV` for `blockD_v`. -/
def PreEpilogueVD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 mpre : Mem) (c : Config) : Prop :=
  PreEpilogueV g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpre c ∧
  MemExtends m0 mpre ∧
  (∀ m' : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mpre[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store)

/-! ## `blockD_v_rec` — the shared epilogue producing `EvalExitD`

`PreEpilogueVD … v → EvalExitD … v`. Reuses `blockD_v` with the carried predicate
`Q m := MemExtends m0 m ∧ [SL.lo,SL.hi)-survival at m` (memory-pure epilogue ⇒
`Q mpre → Q (exit mem)`), then repackages `EvalExit ∧ Q c.σ.mem` into the
`EvalExitD` triple (`MemExtends m0 c.σ.mem` + the identity-`φ` survival witness). -/
theorem blockD_v_rec
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem) :
    Triple
      (fun c => ∃ mpre, PreEpilogueVD g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpre c)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st v sp r sret m0) := by
  intro c hpre
  obtain ⟨mpre, hPre, hMemExt, hSurv⟩ := hpre
  obtain ⟨c', hs, hExit, hMemExt', hSurv'⟩ :=
    blockD_v g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0
      (fun m => MemExtends m0 m ∧
        (∀ m' : Mem, (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store))
      c ⟨mpre, hPre, hMemExt, hSurv⟩
  exact ⟨c', hs, hExit,
    hMemExt', φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hSurv'⟩

end Vsa.Sim

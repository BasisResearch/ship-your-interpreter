import Vsa.Sim.ExecRecCommon
import Vsa.Sim.ExecSeqLoop
import Vsa.Sim.ExecBlockSites

/-!
# Layer 4 — M4 statement family: the `block` case (`ExecS.block`)

This module opens the `ExecS.block` statement case. Its centrepiece — and the
priority deliverable — is **`armExec_rec`**, the statement-recursion multiplier:
the `jal exec_stmt` recursion glue at the block do-while's recursive call
(`0x800041c4`). Where `armTail_rec_es` (`ExecRecCommon.lean`) threads a
`jal eval_expr` ⋈ an *expression* IH into a `SubExecReturn`, `armExec_rec`
threads a `jal exec_stmt` ⋈ a *statement* IH (`ExecIH`, one `exec_stmt` run)
into a `SubStmtReturn` — the state the block loop body holds right after the
recursive `exec_stmt` returns (at the link PC `0x800041c8`), from which it runs
the `bnez a0` status check.

`armExec_rec` is reused by every recursive *statement* case whose body
re-enters `exec_stmt` (block-loop, and — later — if/while/for bodies), exactly
as `armTail_rec_es` is the reusable `jal eval_expr` multiplier for the recursive
*expression*-in-statement cases.

## The recursive call site (block do-while, `0x800041c4`)

At `0x800041c4` the block loop has already staged the recursive call's ABI args
(`a0 = interp*`, `a1 = stmts[i]`, `a2 = innerEnv`, `a3 = retslot`, `sp` lowered
by 176, `i` spilled at `sp+8`), and executes `jal exec_stmt` (link
`0x800041c8`). The callee is `exec_stmt` itself (entry `0x80003fe0`), so this is
a genuine recursion; the induction hypothesis it consumes is an `ExecIH` (one
sub-`exec_stmt` run producing an `ExecExitD`). Its result is a `Status` in `a0`
and — on the `ret` sub-status — a write of the returned `Value` into the sub-retslot.

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

/-! ## `ExecExitD` — the presence/survival-widened `exec_stmt` exit

`ExecExit` strengthened with the two clauses every recursive CALLER needs from
its sub-`exec_stmt`:
1. presence monotonicity (`MemExtends m0 mem`) — the post-call reloads of the
   spill slots and the (possibly written) retslot need presence;
2. an exit-side `StoreRepr` survival clause: the re-represented `st'.store` (at
   ONE coherent extended map pair) tolerates arbitrary further memory changes
   inside the stack region `[SL.lo, SL.hi)` — where the caller's remaining loop
   writes land. Instantiating `m' := c.σ.mem` recovers the plain exit
   `StoreRepr`.

This is the statement-frame analog of `EvalExitD` (`EvalRecCommon.lean`); it is
the shape the real `ExecS` recursor motive must produce. -/
def ExecExitD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (status : Status)
    (sp r aRet : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop :=
  ExecExit g N A SL φf φc nf nc st' status sp r aRet m0 c ∧
  MemExtends m0 c.σ.mem ∧
  ∃ φf' φc' : Addr → Nat,
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store

/-! ## `ExecIH` — the recursive statement-case motive shape

The induction hypothesis a recursive `ExecS` case receives for a
sub-derivation `ExecS st d env s st' status`: the ∀-closed simulation Triple at
the widened exit. This is `InductionScaffold.motive_ExecS` with `ExecExit`
upgraded to `ExecExitD` (RESIDUAL: re-land the leaf/base statement minor
premises at `ExecExitD`). -/
def ExecIH (st : Vsa.While.St) (d : Nat) (env : Addr) (s : Stmt)
    (st' : Vsa.While.St) (status : Status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Triple
      (ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet m0)

/-! ## `SubStmtReturn` — the post-`jal exec_stmt` machine state

What the block loop body knows at the instruction after its recursive
`jal exec_stmt` (link PC `retPC = 0x800041c8`), for a sub-derivation with post
spec state `st'` and produced abrupt-completion `status`:

* control back at `retPC`, `a0 = StatusCode status` (the `bnez a0` reads this),
  `sp` still lowered (`sp - 176`), the four `s0/s1/s2/s3` slots + ra slot
  (`sp-{8,16,24,32,40}`) intact for the loop control and the epilogue;
* the outer callee-saved regs (`s0..s3`, `sp`) restored to the arm frame `garm`
  (`x8 = aStmt` the block node, `x9 = aInterp`, `x18 = aRet` the outer retslot,
  `x19 = aEnv` the inner scope), so the loop can reload `stmts`, `count`, etc.;
* `st'.store` re-represented at ONE coherent extended pair;
* console output `= st'.out`; `exec_stmt`'s code still loaded;
* memory framed to the pre-call memory `mcall` outside
  (stack-window ∪ arena ∪ sub-retslot-window), presence-extended;
* on the `ret v` sub-status, the sub-retslot buffer `[aRetSub, aRetSub+24)`
  holds `ValueRepr v` — the honest fact the enclosing statement (`ret`/return
  propagation) later consumes; other statuses leave it unconstrained.

`garm` is the arm-entry register frame (post-`execBlockA`): `x8 = aStmt`,
`x9 = aInterp`, `x18 = aRet`, `x19 = aEnv`, `x2 = sp`. -/
def SubStmtReturn
    (garm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (status : Status)
    (sp r aRet aRetSub retPC : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (m0 mcall : Mem)
    (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some retPC ∧
  c.σ.regs.get? Register.x10 = some (StatusCode status) ∧   -- a0 = status (for `bnez`)
  c.σ.regs.get? Register.x1 = some retPC ∧
  c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧
  c.σ.regs.get? Register.x18 = some aRet ∧             -- s2 = outer retslot (callee-saved)
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  OutRepr c.σ st' ∧
  -- callee-saved registers (excl s0/s1/s2/s3/sp) restored to the arm frame
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x19 == R) = false →
    (Register.x2 == R) = false → c.σ.regs.get? R = garm R) ∧
  garm Register.x8 = some v8 ∧ garm Register.x9 = some v9 ∧
  garm Register.x18 = some v18 ∧ garm Register.x19 = some v19 ∧ garm Register.x2 = some sp ∧
  (∃ φf' φc' : Addr → Nat,
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store) ∧
  -- on the `ret v` sub-status the sub-retslot holds `ValueRepr v`.
  (∀ v : Value, status = .ret v →
    ∃ φc' : Addr → Nat, PhiExtends φc φc' nc ∧
      ValueRepr c.σ.mem N φc' aRetSub.toNat v) ∧
  Exec_stmtLoaded c.σ.mem ∧
  read64 c.σ.mem (sp.toNat - 8) = some r.toNat ∧
  read64 c.σ.mem (sp.toNat - 16) = some v8.toNat ∧
  read64 c.σ.mem (sp.toNat - 24) = some v9.toNat ∧
  read64 c.σ.mem (sp.toNat - 32) = some v18.toNat ∧
  read64 c.σ.mem (sp.toNat - 40) = some v19.toNat ∧
  -- memory framed to the pre-call memory outside stack ∪ arena ∪ sub-retslot
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRetSub.toNat ≤ a ∧ a < aRetSub.toNat + 24) ∨ c.σ.mem[a]? = mcall[a]?) ∧
  MemExtends mcall c.σ.mem ∧
  -- the pre-call memory equals the arm-entry memory outside the stack window
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?)

/-! ## `armExec_rec` — `jal exec_stmt` ≫ `ExecIH` ⇒ `SubStmtReturn`

The statement-recursion multiplier. From the machine state at the recursive
`jal exec_stmt` PC (`callPC`), with the sub-call's ABI arguments staged
(`a0 = aInterp`, `a1 = aStmtSub` the current `stmts[i]`, `a2 = aEnvSub` the inner
scope, `a3 = aRetSub` the retslot forwarded, `sp` lowered by 176), one `jal`
step lands at `exec_stmt`'s entry with link `retPC = callPC + 4`; the sub-call's
`ExecEntry` is assembled from the loop-body state, the `ExecIH` is applied, and
its `ExecExitD` is repackaged into `SubStmtReturn`.

`garm` is the arm-entry register frame (post-`execBlockA`, before the loop-body
`mv`s of `a0/a1/a2/a3`): `x8 = aStmt`, `x9 = aInterp`, `x18 = aRet`,
`x19 = aEnv`, `x2 = sp`. The loop-body setup only clobbers caller-saved `a*`
registers, so every callee-saved register still reads `garm R`.

The sub-derivation is `ExecS st d envSub sSub st' status` (the current statement
`stmts[i]` in the inner scope `envSub`); `aStmtSub`/`aEnvSub`/`aRetSub` are its
node/scope/retslot machine addresses.  The sub-retslot geometry (an 8-aligned
24-byte RAM slot above HTIF, disjoint from stack/arena/code) is threaded so the
`ret`-sub-status `ValueRepr` survives — it is exactly the shape `ExecEntry`
demands of a `ret`'s retslot. -/
theorem armExec_rec
    (garm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (envSub : Addr) (sSub : Stmt) (status : Status)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r aRet aRetSub aInterp aStmtSub aEnvSub : BitVec 64)
    (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    -- target arithmetic (fixed by the arm, `decide`-able concretely):
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 execStmtEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    -- the per-arm `jal exec_stmt` site step:
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    -- the induction hypothesis for the sub-derivation:
    (hIH : ExecIH st d envSub sSub st' status) :
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        c.σ.regs.get? Register.x10 = some aInterp ∧          -- a0 = interp*
        c.σ.regs.get? Register.x11 = some aStmtSub ∧         -- a1 = stmts[i]
        c.σ.regs.get? Register.x12 = some aEnvSub ∧          -- a2 = inner env
        c.σ.regs.get? Register.x13 = some aRetSub ∧          -- a3 = retslot forwarded
        c.σ.regs.get? Register.x18 = some aRet ∧             -- s2 = outer retslot (survives)
        c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧     -- sp lowered
        (∃ w, c.σ.regs.get? Register.x8 = some w) ∧          -- s0 defined (block node)
        (∃ w, c.σ.regs.get? Register.x9 = some w) ∧          -- s1 defined (interp*)
        (∃ w, c.σ.regs.get? Register.x19 = some w) ∧         -- s3 defined (inner env)
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Exec_stmtLoaded mcall ∧
        StmtRepr mcall aStmtSub.toNat sSub ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        -- callee-saved regs (excl s0/s1/s2/s3/sp) still read the arm frame `garm`
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x19 == R) = false →
          (Register.x2 == R) = false → c.σ.regs.get? R = garm R) ∧
        garm Register.x8 = some v8 ∧ garm Register.x9 = some v9 ∧
        garm Register.x18 = some v18 ∧ garm Register.x19 = some v19 ∧
        garm Register.x2 = some sp ∧
        read64 mcall (sp.toNat - 8) = some r.toNat ∧
        read64 mcall (sp.toNat - 16) = some v8.toNat ∧
        read64 mcall (sp.toNat - 24) = some v9.toNat ∧
        read64 mcall (sp.toNat - 32) = some v18.toNat ∧
        read64 mcall (sp.toNat - 40) = some v19.toNat ∧
        -- sub-statement node geometry (the sub-call's `aStmt`):
        aStmtSub.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmtSub.toNat ∧ aStmtSub.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aStmtSub.toNat ∧
        (aStmtSub.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aStmtSub.toNat) ∧
        -- sub-retslot geometry: an 8-aligned 24-byte RAM slot above HTIF,
        -- disjoint from the sub-call's own stack window `[SL.lo, sp - 176)`:
        aRetSub.toNat % 8 = 0 ∧
        0x80000000 ≤ aRetSub.toNat ∧ aRetSub.toNat + 24 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aRetSub.toNat ∧
        (aRetSub.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aRetSub.toNat) ∧
        -- stack geometry: statement frame (176) + recursive headroom (one
        -- exec_stmt frame + its callee eval frame, 2352 below sp), 16-alignment:
        SL.lo + 2352 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        sp.toNat ≤ 0x100000000 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        r.toNat % 4 = 0 ∧
        -- arena disjoint from the stack window (for the spill/code survival reads):
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        -- exec_stmt code region `[0x80003fe0, 0x80004308)` disjointness (for the
        -- survival of `Exec_stmtLoaded` across the sub-call and the entry `code`):
        (sp.toNat ≤ 0x80003fe0 ∨ 0x80004308 ≤ SL.lo) ∧
        (A.hi ≤ 0x80003fe0 ∨ 0x80004308 ≤ A.lo))
      (SubStmtReturn garm N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet aRetSub retPC
        v8 v9 v18 v19 mcall mcall) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, ha0, hx11, hx12, hx13, hs2, hsp,
    ⟨wx8, hwx8⟩, ⟨wx9, hwx9⟩, ⟨wx19, hwx19⟩, ⟨vmi, hmi⟩, hout, houtStr, hmemc,
    hcodeS, hstmtSub, hstore, hstoreSurv,
    hframe, hgx8, hgx9, hgx18, hgx19, hgx2,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hstAl, hstLo, hstHi, hstWin, hstStk,
    hrsAl, hrsLo, hrsHi, hrsWin, hrsStk,
    hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin, hraAl,
    harenaStk, hexecCodeStk, hexecArenaCode⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp176 : 176 ≤ sp.toNat := by omega
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [h176]; have := sp.isLt; omega
  -- ============ callPC: jal exec_stmt → PC := execStmtEntry, x1 := retPC ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    hjalSite c.σ c.tick c.steps vmi hG hpc hmi (hmemc ▸ hcodeS) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  have hpc1 : σ1.regs.get? Register.PC = some (BitVec.ofNat 64 execStmtEntry) := by
    have := obs_jalT_pc hobs1; rwa [hjaltgt] at this
  have hlink1 : σ1.regs.get? Register.x1 = some retPC := by
    have := obs_jalT_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlink] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some aInterp := obs_jalT_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hx11_1 : σ1.regs.get? Register.x11 = some aStmtSub := obs_jalT_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11
  have hx12_1 : σ1.regs.get? Register.x12 = some aEnvSub := obs_jalT_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hx13_1 : σ1.regs.get? Register.x13 = some aRetSub := obs_jalT_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_jalT_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hs2_1 : σ1.regs.get? Register.x18 = some aRet := obs_jalT_other hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2
  obtain ⟨vmi1, hmi1⟩ := obs_jalT_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_jal]; exact hout
  -- spill-defined for the sub-ExecEntry: s0/s1/s3 present at σ1 (the `jal` writes
  -- only x1/PC/minstret, so the callee-saved regs pass through unchanged).
  have hx8_1 : σ1.regs.get? Register.x8 = some wx8 :=
    obs_jalT_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hwx8
  have hx9_1 : σ1.regs.get? Register.x9 = some wx9 :=
    obs_jalT_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hwx9
  have hx19_1 : σ1.regs.get? Register.x19 = some wx19 :=
    obs_jalT_other hobs1 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hwx19
  -- ============ the sub-call's ExecEntry at ⟨σ1, i1, steps+1⟩ ============
  have hEntry : ExecEntry (fun R => σ1.regs.get? R) N A SL φf φc st d envSub sSub
      (sp - 176#64) retPC aInterp aStmtSub aEnvSub aRetSub mcall ⟨σ1, i1, c.steps + 1⟩ :=
    { good := hG1
      tick := hi1
      pc := hpc1
      a0 := ha0_1
      a1 := hx11_1
      a2 := hx12_1
      a3 := hx13_1
      ra := hlink1
      ra_align := hretAl
      spReg := hsp_1
      stackOK := ⟨by rw [hspsub]; omega, by rw [hspsub]; omega, by rw [hspsub]; omega⟩
      minstret := ⟨vmi1, hmi1⟩
      mem := hmem1e
      code := by show Exec_stmtLoaded σ1.mem; rw [hmem1e]; exact hcodeS
      stmt := by rw [hmem1e]; exact hstmtSub
      store := by rw [hmem1e]; exact hstore
      store_survives := by
        intro m' hag
        refine hstoreSurv m' (fun k hk1 => ?_)
        have hk1' : ¬ (SL.lo ≤ k ∧ k < (sp - 176#64).toNat) := by
          rw [hspsub]; intro ⟨ha, hb⟩; exact hk1 ⟨ha, by omega⟩
        have := hag k hk1'
        rwa [hmem1e] at this
      out := by
        show Vsa.Machine.output σ1 = st.out
        simp only [Vsa.Machine.output]; rw [hout1]; exact houtStr
      frame := fun _ _ => rfl
      code_stack_disjoint := by
        simp only [execStmtEntry, execStmtEnd]
        rcases hexecCodeStk with h | h
        · left; rw [hspsub]; omega
        · right; omega
      stack_ram := ⟨hSLlo, hSLhiRam⟩
      stack_win := hSLwin
      stmt_stack_disjoint := by
        rcases hstStk with h | h
        · left; exact h
        · right; rw [hspsub]; omega
      stmt_align := hstAl
      stmt_ram := ⟨hstLo, hstHi⟩
      stmt_win := hstWin
      spill_defined := ⟨⟨wx8, hx8_1⟩, ⟨wx9, hx9_1⟩, ⟨aRet, hs2_1⟩, ⟨wx19, hx19_1⟩⟩ }
  -- ============ the sub-call (the induction hypothesis) ============
  obtain ⟨c2, hs2', hExitD⟩ :=
    hIH (fun R => σ1.regs.get? R) N A SL φf φc (sp - 176#64) retPC aInterp aStmtSub aEnvSub aRetSub mcall
      ⟨σ1, i1, c.steps + 1⟩ hEntry
  obtain ⟨hExit, hmemExt, φf', φc', hpf', hpc', hstoreSurv'⟩ := hExitD
  -- PC back at the link (ret target of an aligned retPC)
  have hpcRet : c2.σ.regs.get? Register.PC = some retPC := by
    rw [hExit.pc, ret_tgt retPC hretAl]
  -- x1 back at the link `retPC` (exec_stmt restores ra to own link)
  have hx1_2 : c2.σ.regs.get? Register.x1 = some retPC := hExit.ra
  -- a0 = StatusCode status
  have ha0_2 : c2.σ.regs.get? Register.x10 = some (StatusCode status) := hExit.a0
  -- sp restored to lowered value
  have hsp_2 : c2.σ.regs.get? Register.x2 = some (sp - 176#64) := hExit.spReg
  -- frame composition helper
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  -- callee-saved regs at c2 = arm frame `garm` (excl s0/s1/s2/s3/sp).
  have hframe2 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false →
      (Register.x2 == R) = false → c2.σ.regs.get? R = garm R := by
    intro R hR he8 he9 he18 he19 he2
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have hx1R : (Register.x1 == R) = false := abi_ne' (by decide) hab
    have f2 : c2.σ.regs.get? R = σ1.regs.get? R := hExit.frame R hR'
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_jal _ _ _ _ _ _ R hmiR hpcR hx1R hnpcR hmiiR)
    rw [f2, f1]; exact hframe R hR' he8 he9 he18 he19 he2
  -- s2 (x18 = aRet) survives (callee-saved, restored to sub-entry = arm value)
  have hs2_2 : c2.σ.regs.get? Register.x18 = some aRet := by
    have f2 : c2.σ.regs.get? Register.x18 = σ1.regs.get? Register.x18 :=
      hExit.frame Register.x18 (by decide)
    rw [f2]; exact hs2_1
  -- memory agreement outside (stack-window ∪ arena) — sub-retslot ⊂ carve
  have hmemFrame2 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRetSub.toNat ≤ a ∧ a < aRetSub.toNat + 24) ∨ c2.σ.mem[a]? = mcall[a]? := by
    intro a h1 h2
    have := hExit.memFrame a (by rw [hspsub]; intro ⟨ha, hb⟩; exact h1 ⟨ha, by omega⟩) h2
    rcases this with hin | heq
    · left; exact hin
    · right; exact heq
  -- spill slots survive the sub-call (top 40 bytes of the frame: outside the sub
  -- window [SL.lo, sp-176) — wait, spills at sp-{8..40} are IN [SL.lo, sp) but
  -- ABOVE the lowered frame base sp-176, so outside the sub-call's [SL.lo, sp-176)
  -- and outside the sub-retslot carve and arena).
  have hAgTop : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mcall c2.σ.mem := by
    intro k hk
    have := hExit.memFrame k
      (by rw [hspsub]; intro ⟨_, hb⟩; omega)
      (by rcases harenaStk with h | h <;> omega)
    rcases this with hin | heq
    · exact absurd hin (by rcases hrsStk with h | h <;> omega)
    · exact heq.symm
  have hslotRa2 : read64 c2.σ.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotRa
  have hslotS02 : read64 c2.σ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS0
  have hslotS12 : read64 c2.σ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS1
  have hslotS22 : read64 c2.σ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS2
  have hslotS32 : read64 c2.σ.mem (sp.toNat - 40) = some v19.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS3
  -- exec_stmt's code survives (from the exit `code` — StoreRepr independent).
  have hcodeS2 : Exec_stmtLoaded c2.σ.mem := by
    -- the sub-exit re-represents st'.store; exec_stmt code is loaded because the
    -- sub-call preserves it. Draw it from the memFrame: code region disjoint
    -- from stack/arena, and no retslot carve overlaps it.
    refine loaded_exec_stmt_agreeP mcall c2.σ.mem (fun a ha => ?_) hcodeS
    have := hExit.memFrame a
      (by rw [hspsub]; rcases hexecCodeStk with h | h <;> intro ⟨p, q⟩ <;> omega)
      (by rcases hexecArenaCode with h | h <;> omega)
    -- (arena vs code region: `hexecArenaCode`)
    rcases this with hin | heq
    · exact absurd hin (by rcases hrsStk with h | h <;>
        rcases hexecCodeStk with h2 | h2 <;> omega)
    · exact heq.symm
  -- the `ret v` ValueRepr disjunct comes straight from the sub-exit's `retval`.
  refine ⟨c2, (Steps.single hstep1).trans hs2',
    hExit.good, hExit.tick, hpcRet, ha0_2, hx1_2, hsp_2, hs2_2, hExit.minstret,
    hExit.out, hframe2, hgx8, hgx9, hgx18, hgx19, hgx2,
    ⟨φf', φc', hpf', hpc', hstoreSurv' c2.σ.mem (fun _ _ => rfl)⟩,
    hExit.retval,
    hcodeS2, hslotRa2, hslotS02, hslotS12, hslotS22, hslotS32,
    hmemFrame2, hmemExt, fun a _ => rfl⟩

end Vsa.Sim

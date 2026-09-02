import Vsa.Sim.rows.AssemblySkeleton

/-!
# Fleet B6-loopseq — machine-checked obstructions for the 7 loop/seq skeleton holes

The B6-loopseq batch fields (`SkelHSeqNil`/`SkelHSeqConsNormal`/
`SkelHSeqConsAbrupt`/`SkelHFlCondFalse`/`SkelHFlBodyBreak`/`SkelHFlBodyRet`/
`SkelHFlLoop`, `Vsa/Sim/rows/AssemblySkeleton.lean`) are ALL skipped: no landed
supplier can discharge them, and this file certifies the two structural reasons
with kernel-checked lemmas (Law-4 style: the obstruction, not a workaround).

## Obstruction 1 (`ExecSeq` family) — independent `∀ (p q)` + code-free `SegEntry`

`mExecSeq` (`Vsa/Sim/TermSimAssembly.lean:178`) quantifies the entry PC `p` and
exit PC `q` INDEPENDENTLY (its consumers need `p = execSeqLoopPC ≠ q =
execSeqContPC`, so the identity-PC amendment used for `mExecInit` is not
available).  The only landed suppliers for `ExecSeq.nil`
(`ExecSimCommon.execSeqNil`, `LoopScaffoldClose.segIdentity`) are ZERO-STEP
identities — and `zeroStep_segSpan_forces_pc_eq` below proves any zero-step
discharge covers ONLY the diagonal `BitVec.ofNat 64 p = BitVec.ofNat 64 q`.
`skelHSeqNil_offdiag_must_step` then proves any discharge of the hole must
produce a `≥ 1`-step run from EVERY off-diagonal `SegEntry` configuration; but
`SegEntry` (`Vsa/Sim/InductionScaffold.lean:150`) pins NO code byte (no
`code : …Loaded` field, unlike `EvalEntry.code`/`ExecEntry.code`), so no step
is derivable from it — the span is unprovable as stated.  (The `TermAssembly`
supplier note "`execSeqNil` … a `_row` wrap is trivial" is STALE; the committed
`rows/SeqForRows.lean` module doc already records the genuine `p → q` span.)

## Obstruction 2 (`ForLoop` family) — identity-PC motive with store-mutating endpoints

`mForLoop` is an identity-PC span `SegEntry st p → SegExit st' p`, but every
`ForLoop` constructor mutates the spec state (`condFalse` via the cond `EvalE`,
`bodyBreak`/`bodyRet` via the body `ExecS`, `loop` via the whole iteration) —
the DUAL `scaffold-some-motive-unsatisfiable` shape that got
`mExecInit`/`mForCond`/`mExecStep` amended to `True`.
`zeroStep_forSpan_forces_rerepresentation` proves a zero-step discharge forces
the UNCHANGED entry memory `m0` to re-represent the mutated store `st'.store`
(while `SegEntry.store` already pins it to `st.store`) — impossible whenever
`st'` rewrites an existing frame slot; and a `≥ 1`-step discharge is barred by
the same code-free-`SegEntry` fact as Obstruction 1.  The landed engine
(`execForLoopBody`, `ExecFor.lean`) speaks `ExecEntry → ExecExit` and admits NO
adapter in either direction: `SegEntry` cannot supply
`ExecEntry.{pc@execStmtEntry, a0–a3, code, stmt, stackOK}`, and
`ExecSeqExit`/`ExecExit` lack the `memFrame`/`stackWin` fields `SegExit`
demands (the `rows/SeqForRows.lean` seam analysis, re-confirmed here).

Missing suppliers, by name (the coordinator's amendment targets):
providers of `Vsa.Sim.Rows.SeqNilResid` / `SeqConsNormalResid` /
`SeqConsAbruptResid` / `ForResid` (`rows/SeqForRows.lean`) — all unprovable as
stated until `mExecSeq`/`mForLoop` (or `SegEntry`) carry a code-image linkage.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim.ScaffoldRows
open Vsa.Sim.TermSimAssembly
open Vsa.Sim.Scaffold
local notation "SpecSt" => Vsa.While.St

namespace Vsa.Sim.B6LoopSeqObstruction

/-- **Obstruction 1a** — a ZERO-STEP discharge of any `SegEntry → SegExit` span
(the shape of `mExecSeq`) covers only the PC diagonal: one config satisfying
both endpoint predicates forces `BitVec.ofNat 64 p = BitVec.ofNat 64 q`.  So
the landed identity suppliers (`ExecSimCommon.execSeqNil`,
`LoopScaffoldClose.segIdentity`) cannot reach `mExecSeq`'s independent `q`. -/
theorem zeroStep_segSpan_forces_pc_eq
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d dLeft aLeft p q nf nc : Nat) (m0 : Mem) (c : Config)
    (he : SegEntry g N A SL φf φc st d dLeft aLeft p m0 c)
    (hx : SegExit g N A SL φf φc nf nc st' q m0 c) :
    BitVec.ofNat 64 p = BitVec.ofNat 64 q :=
  Option.some.inj (he.pc.symm.trans hx.pc)

/-- **Obstruction 1b** — any discharge of the `SkelHSeqNil` hole must, at every
off-diagonal `(p, q)`, produce a run of `≥ 1` machine steps (`c' ≠ c`) from
EVERY `SegEntry` configuration.  `SegEntry` pins no code byte at `p` (no
`code` field), so no such step is derivable from the hypothesis set — the hole
is unprovable with the landed suppliers. -/
theorem skelHSeqNil_offdiag_must_step (L : Layout)
    (h : Vsa.Sim.TermAssembly.Skel.SkelHSeqNil L)
    (st : SpecSt) (d : Nat) (env : Addr)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft p q : Nat) (m0 : Mem)
    (hpq : BitVec.ofNat 64 p ≠ BitVec.ofNat 64 q)
    (c : Config)
    (hc : SegEntry g N A SL φf φc st d dLeft aLeft p m0 c) :
    ∃ c', c' ≠ c ∧ Steps c c' ∧
      SegExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st q m0 c' := by
  obtain ⟨c', hs, hx⟩ :=
    h st d env g N A SL φf φc dLeft aLeft p q m0 c hc
  refine ⟨c', ?_, hs, hx⟩
  rintro rfl
  exact hpq (zeroStep_segSpan_forces_pc_eq g N A SL φf φc st st d dLeft aLeft
    p q st.store.frames.size st.store.closures.size m0 c' hc hx)

/-- **Obstruction 2** — a ZERO-STEP discharge of the identity-PC `mForLoop`
span forces the UNCHANGED entry memory `m0` to re-represent the MUTATED spec
store `st'.store` (with φ-maps extended over the entry sizes), while
`SegEntry.store` already pins `m0` to `st.store`.  Whenever a `ForLoop`
endpoint rewrites an existing frame slot the two representations conflict —
so the `hFl*` holes cannot be closed by identity, and a stepping proof is
barred by the code-free `SegEntry` (Obstruction 1b's fact). -/
theorem zeroStep_forSpan_forces_rerepresentation
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d dLeft aLeft p nf nc : Nat) (m0 : Mem) (c : Config)
    (he : SegEntry g N A SL φf φc st d dLeft aLeft p m0 c)
    (hx : SegExit g N A SL φf φc nf nc st' p m0 c) :
    StoreRepr m0 N A φf φc st.store ∧
    ∃ (φf' φc' : Addr → Nat),
      PhiExtends φf φf' nf ∧ PhiExtends φc φc' nc ∧
      StoreRepr m0 N A φf' φc' st'.store := by
  have hmem := he.mem
  refine ⟨hmem ▸ he.store, ?_⟩
  obtain ⟨φf', φc', h1, h2, h3⟩ := hx.store
  exact ⟨φf', φc', h1, h2, hmem ▸ h3⟩

#print axioms zeroStep_segSpan_forces_pc_eq
#print axioms skelHSeqNil_offdiag_must_step
#print axioms zeroStep_forSpan_forces_rerepresentation

end Vsa.Sim.B6LoopSeqObstruction

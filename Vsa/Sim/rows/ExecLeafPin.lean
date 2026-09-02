import Vsa.Sim.rows.ExecLeafD
import Vsa.Sim.rows.EntryGroundRows
import Vsa.Sim.rows.AssemblySkeleton

/-!
# `ExecLeafPin` — the X3 exec-leaf re-seat scaffold (Wave 48b)

The pinned re-seat of the register-only exec leaves (`brk`/`cont`) at
`ExecExitPinned`, the exec twin of the wave-47e eval re-seat
(`evalIntSimP`/`leafWidenP_of_entry`, `EvalLeafD.lean`).  `ExecLeafD.lean`
(wave 48a) already landed the entry-derivable half:

* `ExecLeafMemPin` / `ExecExitPinned` / `ExecLeafWidenP` — the pinned exit family
  and its widener;
* `execLeafWidenP_of_entry` — **the pinned widener from the `ExecEntry` alone**
  (it forwards the pin conjunct `hx.2.pres` that `ExecExitPinned` bundles);
* `execExitD_of_pinnedExecExit` — the pinned-family → `ExecExitD` bridge.

This file assembles those into the pinned leaf sims + rows and reduces
`field_hSBrk`/`field_hSCont` (`assembly_skeleton.tsv` holes) to ONE named
premise, exactly as wave 47g reduced `hStr` to `EvalEntryStrAstRegion` before its
interface landed.

## The single named premise (Law 2/4) — `ExecArmMemExt`

`execBrkSim`/`execContSim` (`ExecBrkCont.lean`) conclude the PLAIN `ExecExit`.
To conclude the PINNED `ExecExitPinned` they must additionally establish
`ExecLeafMemPin SL sp m0 c'.σ.mem` on the reached exit `c'`, whose two fields are:

* `agree` — `∀ k, ¬(SL.lo ≤ k < sp) → c'.σ.mem[k]? = m0[k]?`.  This is TRUE and
  internally available: `execBlockD` proves the epilogue LOADS leave memory
  unchanged (`hmem7e : σ7.mem = mpre`, `ExecBrkCont.lean:398`) and both
  `ExecArmEntryK`/`PreExecEpilogue` carry the FULL (no-arena-exclusion)
  `hmemframe : ∀ k, ¬(SL.lo ≤ k < sp) → mem[k]? = m0[k]?` (`:234`/`:188`),
  threaded to the exit as `hmem7e ▸ hmemframe`.
* `pres` — `MemExtends m0 c'.σ.mem`.  This is the ONE genuinely-missing fact.
  The exit memory is `m0` plus the five prologue `writeMap8` spills — presence-
  preserving — so `MemExtends m0 c'.σ.mem` is TRUE; but its proof needs the
  prologue write chain (`σ2..σ6 = writeMap8^5 m0`, `ExecBrkCont.lean:621-711`),
  which lives INSIDE `execBlockA` and is NOT exposed by `ExecArmEntryK` (whose
  memory clause is only the m0-*agreement* frame, not presence monotonicity).

**Machine-checked obstruction (Law 4).**  Exposing `MemExtends m0 ment` from
`execBlockA` is the exec twin of the wave-47e eval move that amended `blockA_k`'s
post to carry `MemExtends m0 ment` (`EvalSimCommon.lean:907`).  On the exec side
that amendment lands the fact into the SHARED `ExecArmEntryK` ∧-tower, whose
positional destructures/constructions fan out across ~10 files
(`ExecBrkCont`/`ExecDispatch`/`ExecRecCommon` + the six `Stmt*ArmStagePre`
rows) — an ITEM-ZERO-scale coupled amendment (the 48a report names it "its own
≤1-session task").  It is NOT safely completable inside this bounded gate under
one lean process without risking the green tree, so it is named here as ONE typed
premise `ExecArmMemExt` and everything ELSE is machine-checked around it.

The exit's stack-frame *agreement* clause (`ExecLeafMemPin.agree`) is ALSO only
narrowly available from the plain `ExecExit`: `ExecExit.memFrame` excludes the
arena, whereas the pin's `agree` is arena-inclusive (brk/cont provably write no
arena byte — `ExecBrkCont.lean:233`).  So the named premise bundles the WHOLE
pin `ExecLeafMemPin SL sp m0 c'.σ.mem` on the reached exit — precisely the object
the `execBlockA` presence exposure + the internal `hmem7e ▸ hmemframe` frame jointly
supply.  Once `execBlockA` exposes `MemExtends m0 ment`, this residual is a
documented one-liner (the pin `= ⟨that MemExtends, hmem7e ▸ hmemframe⟩`) and the two
fields flip.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  `#print axioms` ⊆
{propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.Rows

local notation "SpecSt" => Vsa.While.St

/-! ## The named premise — the exec-leaf exit pin residual

For any leaf exit (`ExecExit` at PC = ret target, mem = the prologue-spilled
`mpre`), the exec-leaf memory pin `ExecLeafMemPin SL sp m0 mem` holds: `pres`
(presence monotonicity, the write-chain fact `execBlockA` must expose) and `agree`
(the internal `hmem7e ▸ hmemframe`, arena-inclusive).  Quantified exit-side so the
pinned sim consumes it directly. -/
def ExecArmMemExt (st : SpecSt) (status : Status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aRet : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st status sp r aRet m0 c →
    Vsa.Sim.ExecLeafMemPin SL sp m0 c.σ.mem

/-! ## Pinned leaf sims — `execBrkSim`/`execContSim` re-seated at `ExecExitPinned`

Wrap the landed `execBrkSim`/`execContSim` output (the plain `ExecExit` `Triple`)
into a `Triple` at the pinned exit `ExecExitPinned = ExecExit ∧ ExecLeafMemPin`,
supplying the pin from the `ExecArmMemExt` residual. -/

/-- **`execBrkSimP`** — `ExecS.brk` at the PINNED exit.  Wraps `execBrkSim`
(`ExecBrkCont.lean`) with the exit pin from `ExecArmMemExt`. -/
theorem execBrkSimP
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (hSpec : ExecS st d env .brk st .brk)
    (hslot : Vsa.Sim.StmtSlotPinned 7 Vsa.Sim.execArmBrk m0)
    (htableStk : Vsa.Sim.stmtJumpTableBase + 4 * 7 + 4 ≤ SL.lo ∨
      sp.toNat ≤ Vsa.Sim.stmtJumpTableBase + 4 * 7)
    (hMemExt : ExecArmMemExt st .brk) :
    Triple
      (fun c => Vsa.Sim.ExecEntry g N A SL φf φc st d env .brk sp r aInterp aStmt aEnv aRet m0 c
        ∧ c.σ.sailOutput = out0)
      (Vsa.Sim.ExecExitPinned g N A SL φf φc st .brk sp r aRet m0) := by
  intro c hpre
  obtain ⟨c', hs, hExit⟩ :=
    Vsa.Sim.execBrkSim g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 out0 hSpec hslot htableStk c hpre
  exact ⟨c', hs, hExit, hMemExt g N A SL φf φc sp r aRet m0 c' hExit⟩

/-- **`execContSimP`** — `ExecS.cont` at the PINNED exit. -/
theorem execContSimP
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (hSpec : ExecS st d env .cont st .cont)
    (hslot : Vsa.Sim.StmtSlotPinned 8 Vsa.Sim.execArmCont m0)
    (htableStk : Vsa.Sim.stmtJumpTableBase + 4 * 8 + 4 ≤ SL.lo ∨
      sp.toNat ≤ Vsa.Sim.stmtJumpTableBase + 4 * 8)
    (hMemExt : ExecArmMemExt st .cont) :
    Triple
      (fun c => Vsa.Sim.ExecEntry g N A SL φf φc st d env .cont sp r aInterp aStmt aEnv aRet m0 c
        ∧ c.σ.sailOutput = out0)
      (Vsa.Sim.ExecExitPinned g N A SL φf φc st .cont sp r aRet m0) := by
  intro c hpre
  obtain ⟨c', hs, hExit⟩ :=
    Vsa.Sim.execContSim g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 out0 hSpec hslot htableStk c hpre
  exact ⟨c', hs, hExit, hMemExt g N A SL φf φc sp r aRet m0 c' hExit⟩

/-! ## The `*D` reseat at the pinned widener — `mExecS`-motive rows

`execBrkSimDP`/`execContSimDP` produce the `ExecExitD` the recursor motive
consumes, threading the pinned widener `ExecLeafWidenP` (entry-derivable via
`execLeafWidenP_of_entry`) and the pin from `ExecArmMemExt`. -/

/-- **`execBrkSimDP`** — `ExecS.brk` at `ExecExitD` (the `ExecIH` shape), pinned. -/
theorem execBrkSimDP
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hE : ExecS st d env .brk st .brk)
    (hslot : Vsa.Sim.StmtSlotPinned 7 Vsa.Sim.execArmBrk m0)
    (htableStk : Vsa.Sim.stmtJumpTableBase + 4 * 7 + 4 ≤ SL.lo ∨
      sp.toNat ≤ Vsa.Sim.stmtJumpTableBase + 4 * 7)
    (hMemExt : ExecArmMemExt st .brk) :
    Triple
      (Vsa.Sim.ExecEntry g N A SL φf φc st d env .brk sp r aInterp aStmt aEnv aRet m0)
      (Vsa.Sim.ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st .brk sp r aRet m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExitP⟩ :=
    execBrkSimP g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 c.σ.sailOutput
      hE hslot htableStk hMemExt c ⟨hEntry, rfl⟩
  exact ⟨c', hs, Vsa.Sim.execExitD_of_pinnedExecExit hExitP (Vsa.Sim.execLeafWidenP_of_entry hEntry)⟩

/-- **`execContSimDP`** — `ExecS.cont` at `ExecExitD`, pinned. -/
theorem execContSimDP
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hE : ExecS st d env .cont st .cont)
    (hslot : Vsa.Sim.StmtSlotPinned 8 Vsa.Sim.execArmCont m0)
    (htableStk : Vsa.Sim.stmtJumpTableBase + 4 * 8 + 4 ≤ SL.lo ∨
      sp.toNat ≤ Vsa.Sim.stmtJumpTableBase + 4 * 8)
    (hMemExt : ExecArmMemExt st .cont) :
    Triple
      (Vsa.Sim.ExecEntry g N A SL φf φc st d env .cont sp r aInterp aStmt aEnv aRet m0)
      (Vsa.Sim.ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st .cont sp r aRet m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExitP⟩ :=
    execContSimP g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 c.σ.sailOutput
      hE hslot htableStk hMemExt c ⟨hEntry, rfl⟩
  exact ⟨c', hs, Vsa.Sim.execExitD_of_pinnedExecExit hExitP (Vsa.Sim.execLeafWidenP_of_entry hEntry)⟩

/-! ## The field discharges — `BrkResid`/`ContResid` from `ExecEntry` + the pin

`BrkResid`/`ContResid` (`ExecRouting.lean`) demand the PLAIN `ExecCaseGeom`
(slot pin + table disjointness + plain `ExecLeafWiden`).  The slot/table halves
come from `ExecEntry.ground` (`execGround_caseGeom_brk`/`_cont`, wave 47i); the
plain `ExecLeafWiden` (`Widen` over the plain `ExecExit`) is built from the entry
survival + the pin residual — `pres` is the pin's `pres`, `surv` re-represents
`st.store` over any change confined to `stackFoot SL`, using the pin's `agree` to
push it outside the `[SL.lo, sp)` window the entry survival covers.  This is the
exec twin of the plain `LeafWiden` construction on the eval side. -/

/-- The plain `ExecLeafWiden` over `ExecExit`, from the entry + the pin residual. -/
theorem execLeafWiden_of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr} {s : Stmt} {status : Status}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {c : Config}
    (hc : Vsa.Sim.ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c)
    (hMemExt : ExecArmMemExt st status) :
    Vsa.Sim.ExecLeafWiden g N A SL φf φc st status sp r aRet m0 where
  pres := fun c' hx => (hMemExt g N A SL φf φc sp r aRet m0 c' hx).pres
  surv := fun c' hx =>
    ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, fun m' hm' => by
      refine hc.store_survives m' (fun k hk => ?_)
      have hksp : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun hcon =>
        hk ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hc.stackOK.2.1⟩
      rw [hc.mem]
      exact ((hMemExt g N A SL φf φc sp r aRet m0 c' hx).agree k hksp).symm.trans (hm' k hk)⟩

/-- **`field_hSBrk`** — `∀ st, BrkResid st`, MODULO the `ExecArmMemExt` premise
(`hBrkPin`, the pin residual `execBlockA` must expose; see the header).  The slot
pin + table disjunct come from `ExecEntry.ground` (wave 47i); the widener from
`execLeafWiden_of_entry`. -/
theorem field_hSBrk (hBrkPin : ∀ st, ExecArmMemExt st .brk) :
    ∀ st, BrkResid st :=
  fun st _g _N _A _SL _φf _φc _d _env _sp _r _aInterp _aStmt _aEnv _aRet _m0 _c hc =>
    ⟨hc.mem ▸ (Vsa.Sim.Rows.execGround_caseGeom_brk hc.ground).1,
     (Vsa.Sim.Rows.execGround_caseGeom_brk hc.ground).2,
     execLeafWiden_of_entry hc (hBrkPin st)⟩

/-- **`field_hSCont`** — `∀ st, ContResid st`, MODULO `hContPin`. -/
theorem field_hSCont (hContPin : ∀ st, ExecArmMemExt st .cont) :
    ∀ st, ContResid st :=
  fun st _g _N _A _SL _φf _φc _d _env _sp _r _aInterp _aStmt _aEnv _aRet _m0 _c hc =>
    ⟨hc.mem ▸ (Vsa.Sim.Rows.execGround_caseGeom_cont hc.ground).1,
     (Vsa.Sim.Rows.execGround_caseGeom_cont hc.ground).2,
     execLeafWiden_of_entry hc (hContPin st)⟩

/-- The skeleton-hole form (`assembly_skeleton.tsv` row `hSBrk`), modulo the pin. -/
theorem skelHSBrk_of_pin (L : Vsa.Refine.Layout) (hBrkPin : ∀ st, ExecArmMemExt st .brk) :
    Vsa.Sim.TermAssembly.Skel.SkelHSBrk L :=
  field_hSBrk hBrkPin

/-- The skeleton-hole form for `hSCont`, modulo the pin. -/
theorem skelHSCont_of_pin (L : Vsa.Refine.Layout) (hContPin : ∀ st, ExecArmMemExt st .cont) :
    Vsa.Sim.TermAssembly.Skel.SkelHSCont L :=
  field_hSCont hContPin

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.execBrkSimP
#print axioms Vsa.Sim.Rows.execContSimP
#print axioms Vsa.Sim.Rows.execBrkSimDP
#print axioms Vsa.Sim.Rows.execContSimDP
#print axioms Vsa.Sim.Rows.execLeafWiden_of_entry
#print axioms Vsa.Sim.Rows.field_hSBrk
#print axioms Vsa.Sim.Rows.field_hSCont

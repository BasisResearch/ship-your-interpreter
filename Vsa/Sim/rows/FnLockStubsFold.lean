import Vsa.Sim.rows.FnRetarget_lock_acquire_recursive
import Vsa.Sim.rows.FnRetarget_lock_release_recursive
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.ChainFactsTac

/-!
# The retarget lock stubs — whole-function summaries (run1 io lane)

`__retarget_lock_acquire_recursive` (`0x80006fe0`) and
`__retarget_lock_release_recursive` (`0x80006ff8`) are single-`ret` stubs —
every newlib `_X_r` io function calls them around its FILE work.  Their
summaries are the degenerate case of the gen_fn fold: ONE jr-terminated seg,
nothing written, everything transported.

The summaries are GENERIC in the caller's keep list (`keep : GRegs`): the
stub writes no register, so any valid GPR keep set survives — the caller
discharges the `FrameOK` side condition with one `decide` at its concrete
keep list (a-regs INCLUDED: nothing clobbers them here, unlike a real call).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/-! ## The shared ret-stub pre/post shape -/

/-- Parked at a ret-stub's entry: `ra = ra0`, the caller's keep list held,
memory/console/HTIF mailbox as given. -/
structure RetStubPre (ra0 : BitVec 64) (keep : GRegs)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) (pwv : BitVec 4)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = m0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  ra : gprGet c.σ 1 = some ra0
  keep : GHolds c.σ keep
  out : c.σ.sailOutput = out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some pwv
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Returned to `ra0`: NOTHING else changed — memory, console, HTIF mailbox,
`ra`, and the whole keep list are as at entry. -/
structure RetStubPost (ra0 : BitVec 64) (keep : GRegs)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) (pwv : BitVec 4)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some ra0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  ra : gprGet c.σ 1 = some ra0
  keep : GHolds c.σ keep
  out : c.σ.sailOutput = out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some pwv
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-! ## `__retarget_lock_acquire_recursive` -/

/-- The one seg's `ChainFacts`: just the jr return-target alignment. -/
theorem lockAcq_facts (ra0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hcode : Vsa.Sim.Code.__retarget_lock_acquire_recursiveLoaded m0)
    (hfix : BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1 = ra0)
    (halign : ra0.toNat % 4 = 0) :
    ChainFacts m0 m0 (retarget_lock_acquire_recursiveX6fe0L ra0) []
      retarget_lock_acquire_recursiveX6fe0Seg := by
  chain_facts hcode with "Vsa.Sim.Code.__retarget_lock_acquire_recursive_at_"
  · show (BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [hfix]; exact halign

/-- **The `__retarget_lock_acquire_recursive` summary**: a pure `ret` — control
returns to `ra0`, nothing else changes.  Generic in the caller's `keep` list;
the caller supplies its `FrameOK` by one `decide`. -/
theorem lockAcquire_summary (ra0 : BitVec 64) (keep : GRegs)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) (pwv : BitVec 4)
    (hok : FrameOK (keysG keep) retarget_lock_acquire_recursiveX6fe0Seg)
    (hcode : Vsa.Sim.Code.__retarget_lock_acquire_recursiveLoaded m0)
    (hfix : BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1 = ra0)
    (halign : ra0.toNat % 4 = 0) :
    FnSummary 0x80006fe0#64 (RetStubPre ra0 keep m0 out0 pwv)
      (RetStubPost ra0 keep m0 out0 pwv) := by
  refine ⟨?_⟩
  have T := segRowFramed retarget_lock_acquire_recursiveX6fe0Seg
    (retarget_lock_acquire_recursiveX6fe0L ra0) []
    0x80006fe0#64 m0 keep out0 pwv
    (by show ChainOK 0x80006fe0#64 [1] retarget_lock_acquire_recursiveX6fe0Seg
        decide)
    hok
  intro c hc
  obtain ⟨hpc, hp⟩ := hc
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hp.good, hp.mem, hpc, hp.minstret, ⟨hp.ra, trivial⟩,
        by show KeysOK [1]; decide,
        by rw [hp.mem]; exact lockAcq_facts ra0 m0 hcode hfix halign, hp.tick⟩
      keep := hp.keep
      out := hp.out
      pw := hp.pw
      th := hp.th }
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem]; rfl
      pc := by
        rw [h1.pc]
        show some (BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1)
          = some ra0
        rw [hfix]
      minstret := h1.minstret
      ra := gholds_lookup (v := ra0) _ h1.regs (by rfl)
      keep := h1.keep
      out := h1.out
      pw := h1.pw
      th := h1.th }

#print axioms lockAcquire_summary

/-! ## `__retarget_lock_release_recursive` -/

theorem lockRel_facts (ra0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hcode : Vsa.Sim.Code.__retarget_lock_release_recursiveLoaded m0)
    (hfix : BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1 = ra0)
    (halign : ra0.toNat % 4 = 0) :
    ChainFacts m0 m0 (retarget_lock_release_recursiveX6ff8L ra0) []
      retarget_lock_release_recursiveX6ff8Seg := by
  chain_facts hcode with "Vsa.Sim.Code.__retarget_lock_release_recursive_at_"
  · show (BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [hfix]; exact halign

/-- **The `__retarget_lock_release_recursive` summary** — identical shape. -/
theorem lockRelease_summary (ra0 : BitVec 64) (keep : GRegs)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) (pwv : BitVec 4)
    (hok : FrameOK (keysG keep) retarget_lock_release_recursiveX6ff8Seg)
    (hcode : Vsa.Sim.Code.__retarget_lock_release_recursiveLoaded m0)
    (hfix : BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1 = ra0)
    (halign : ra0.toNat % 4 = 0) :
    FnSummary 0x80006ff8#64 (RetStubPre ra0 keep m0 out0 pwv)
      (RetStubPost ra0 keep m0 out0 pwv) := by
  refine ⟨?_⟩
  have T := segRowFramed retarget_lock_release_recursiveX6ff8Seg
    (retarget_lock_release_recursiveX6ff8L ra0) []
    0x80006ff8#64 m0 keep out0 pwv
    (by show ChainOK 0x80006ff8#64 [1] retarget_lock_release_recursiveX6ff8Seg
        decide)
    hok
  intro c hc
  obtain ⟨hpc, hp⟩ := hc
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hp.good, hp.mem, hpc, hp.minstret, ⟨hp.ra, trivial⟩,
        by show KeysOK [1]; decide,
        by rw [hp.mem]; exact lockRel_facts ra0 m0 hcode hfix halign, hp.tick⟩
      keep := hp.keep
      out := hp.out
      pw := hp.pw
      th := hp.th }
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem]; rfl
      pc := by
        rw [h1.pc]
        show some (BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1)
          = some ra0
        rw [hfix]
      minstret := h1.minstret
      ra := gholds_lookup (v := ra0) _ h1.regs (by rfl)
      keep := h1.keep
      out := h1.out
      pw := h1.pw
      th := h1.th }

#print axioms lockRelease_summary

end Vsa.Sim

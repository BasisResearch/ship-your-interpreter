import Vsa.Sim.rows.FnFflushRFold
import Vsa.Sim.rows.FnSflushREffect

/-! Memory effects of the successful one-byte `_fflush_r` summary. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim

theorem fflushPrefixM_getElem (g : FflushG) (hg : FflushGOk g) (a : Nat)
    (hstack : a < g.sp.toNat - 32 ∨ g.sp.toNat ≤ a) :
    (fflushPrefixM g)[a]? = g.m0[a]? := by
  have he := fflush_spE_toNat g.sp hg.stack
  have h0 : a < (fflushSpE g.sp).toNat ∨
      (fflushSpE g.sp).toNat + 8 ≤ a := by
    rw [he]
    have := hg.stack.lo
    omega
  have hslot (off : Nat) (hoff : off ≤ 24) :
      a < (fflushSpE g.sp + BitVec.ofNat 64 off).toNat ∨
      (fflushSpE g.sp + BitVec.ofNat 64 off).toNat + 8 ≤ a := by
    rw [fflush_slot_toNat g.sp hg.stack off (by omega)]
    have := hg.stack.lo
    omega
  unfold fflushPrefixM fflushAcquireM
  rw [show sign_extend (m := 64) (8#12) = 8#64 by decide,
    show sign_extend (m := 64) (24#12) = 24#64 by decide,
    getElem_writeMap8_disjoint _ _ a _ h0,
    getElem_writeMap8_disjoint _ _ a _ h0,
    getElem_writeMap8_disjoint _ _ a _ (hslot 8 (by decide)),
    getElem_writeMap8_disjoint _ _ a _ (hslot 24 (by decide))]

theorem fflushReleaseM_getElem (g : FflushG) (hg : FflushGOk g) (a : Nat)
    (hstack : a < g.sp.toNat - 128 ∨ g.sp.toNat ≤ a)
    (hcursor : a < consoleStdout ∨ consoleStdout + 8 ≤ a)
    (hcount : a < consoleStdout + 12 ∨ consoleStdout + 16 ≤ a)
    (herrno : a < wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ a) :
    (fflushReleaseM g)[a]? = g.m0[a]? := by
  have he := fflush_spE_toNat g.sp hg.stack
  have h0 : a < (fflushSpE g.sp).toNat ∨
      (fflushSpE g.sp).toNat + 8 ≤ a := by
    rw [he]
    have := hg.stack.lo
    omega
  unfold fflushReleaseM
  rw [getElem_writeMap8_disjoint _ _ a _ h0]
  exact (sflushCallbackM_getElem (fflushSG g) (fflushSG_ok g hg) a
    (by
      change a < (fflushSpE g.sp).toNat - 96 ∨ (fflushSpE g.sp).toNat ≤ a
      rw [he]
      omega) hcursor hcount herrno).trans
    (fflushPrefixM_getElem g hg a (by omega))

/-- `_fflush_r` adds a 32-byte frame around `__sflush_r` and writes its
release argument into that frame. All non-stack writes come from the child. -/
def FflushWriteFoot (sp : BitVec 64) (a : Nat) : Prop :=
  (sp.toNat - 128 ≤ a ∧ a < sp.toNat) ∨
  (consoleStdout ≤ a ∧ a < consoleStdout + 8) ∨
  (consoleStdout + 12 ≤ a ∧ a < consoleStdout + 16) ∨
  (wrErrnoAddr ≤ a ∧ a < wrErrnoAddr + 4)

theorem FflushFnPost.mem_frame {g : FflushG} {c : Config}
    (h : FflushFnPost g c) (hg : FflushGOk g) :
    AgreeP (fun a => ¬ FflushWriteFoot g.sp a) c.σ.mem g.m0 := by
  intro a ha
  rw [h.mem]
  simp only [FflushWriteFoot, not_or] at ha
  exact fflushReleaseM_getElem g hg a (by omega) (by omega) (by omega) (by omega)

theorem fflushReleaseM_console_agree (g : FflushG) (hg : FflushGOk g)
    (a : Nat) (ha : ConsoleFoot a) :
    (fflushReleaseM g)[a]? = (fflushAfterSflushM g)[a]? := by
  apply getElem_writeMap8_disjoint
  left
  have hb := consoleFoot_lt_stdout_end a ha
  have hs := hg.stack.nested.console
  omega

theorem FflushFnPost.console {g : FflushG} {c : Config}
    (h : FflushFnPost g c) (hg : FflushGOk g) :
    ConsoleStream c.σ.mem := by
  rw [h.mem]
  exact ConsoleStream.of_agree (fflushReleaseM_console_agree g hg)
    (sflushCallbackM_console (fflushSG g) (fflushSG_ok g hg))

theorem FflushFnPost.buffer_eq {g : FflushG} {c : Config}
    (h : FflushFnPost g c) (hg : FflushGOk g) :
    c.σ.mem[consoleBuf]? = g.m0[consoleBuf]? := by
  have hb : ConsoleFoot consoleBuf := Or.inr (Or.inr (Or.inr rfl))
  rw [h.mem]
  exact (fflushReleaseM_console_agree g hg consoleBuf hb).trans
    (((sflushCallbackM_console_agree (fflushSG g) (fflushSG_ok g hg)
      consoleBuf hb).trans (sflushClosedM_buffer (fflushSG g) (fflushSG_ok g hg))).trans
      hg.console.bufferByte.symm)

#print axioms FflushFnPost.mem_frame
#print axioms FflushFnPost.console
#print axioms FflushFnPost.buffer_eq

end Vsa.Sim

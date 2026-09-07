import Vsa.Sim.rows.FnSflushRSuffix

/-!
Memory effects of the successful one-byte `__sflush_r` summary.
The callback restores the FILE flags. Cursor/count stores and the errno clear
remain visible; the input buffer byte survives this flush.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim

theorem sflushClosedM_getElem (g : SflushG) (hg : SflushGOk g) (a : Nat)
    (hstack : a < g.sp.toNat - 48 ∨ g.sp.toNat ≤ a)
    (hcursor : a < consoleStdout ∨ consoleStdout + 8 ≤ a)
    (hcount : a < consoleStdout + 12 ∨ consoleStdout + 16 ≤ a) :
    (sflushClosedM g)[a]? = g.m0[a]? := by
  have hslot (off : Nat) (hoff : off ≤ 40) :
      a < (sflushSpE g.sp + BitVec.ofNat 64 off).toNat ∨
      (sflushSpE g.sp + BitVec.ofNat 64 off).toNat + 8 ≤ a := by
    rw [sflush_slot_toNat g.sp hg.stack off (by omega) (by omega)]
    have := hg.stack.htif
    have ht : tohostAddr = 0x8001ad00 := rfl
    omega
  have h8 := hslot 8 (by decide)
  have h16 := hslot 16 (by decide)
  have h24 := hslot 24 (by decide)
  have h32 := hslot 32 (by decide)
  have h40 := hslot 40 (by decide)
  unfold sflushClosedM sflushM4 sflushM3 sflushM2 sflushM1 sflushEntryLog writeLog
  simp only [List.foldl_cons, List.foldl_nil, applyW]
  rw [show sign_extend (m := 64) (8#12) = 8#64 by decide,
    show sign_extend (m := 64) (16#12) = 16#64 by decide,
    show sign_extend (m := 64) (24#12) = 24#64 by decide,
    show sign_extend (m := 64) (32#12) = 32#64 by decide,
    show sign_extend (m := 64) (40#12) = 40#64 by decide]
  rw [getElem_writeMap4_disjoint _ _ a _ hcount,
    getElem_writeMap8_disjoint _ _ a _ hcursor,
    getElem_writeMap8_disjoint _ _ a _ h24,
    getElem_writeMap8_disjoint _ _ a _ h16,
    getElem_writeMap8_disjoint _ _ a _ h40,
    getElem_writeMap8_disjoint _ _ a _ h8,
    getElem_writeMap8_disjoint _ _ a _ h32]

/-- The exact summary memory agrees outside its stack window, cursor/count,
and errno. In particular the flags halfword is restored to its entry value. -/
theorem sflushCallbackM_getElem (g : SflushG) (hg : SflushGOk g) (a : Nat)
    (hstack : a < g.sp.toNat - 96 ∨ g.sp.toNat ≤ a)
    (hcursor : a < consoleStdout ∨ consoleStdout + 8 ≤ a)
    (hcount : a < consoleStdout + 12 ∨ consoleStdout + 16 ≤ a)
    (herrno : a < wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ a) :
    (sflushCallbackM g)[a]? = g.m0[a]? := by
  have hsw := sflushSWG_ok g hg
  have hwr := swWRG_ok (sflushSWG g) hsw
  have hsp := sflush_spE_toNat g.sp hg.stack
  have hwrstep : (sflushCallbackM g)[a]? = (swM2 (sflushSWG g))[a]? := by
    apply wrM1_getElem_lo (swWRG (sflushSWG g)) hwr a
    · change a < (sflushSpE g.sp).toNat - 16 ∨ (sflushSpE g.sp).toNat ≤ a
      rw [hsp]
      omega
    · exact herrno
  by_cases h0 : a = consoleStdout + 16
  · subst a
    exact hwrstep.trans ((sflushSwM2_flag0 g hg).trans hg.console.flag0.symm)
  by_cases h1 : a = consoleStdout + 17
  · subst a
    exact hwrstep.trans ((sflushSwM2_flag1 g hg).trans hg.console.flag1.symm)
  have hswstep := swM2_getElem_lo (sflushSWG g) hsw a
    (by
      change a < (sflushSpE g.sp).toNat - 8 ∨ (sflushSpE g.sp).toNat ≤ a
      rw [hsp]
      omega)
    (by
      change a < consoleStdout + 16 ∨ consoleStdout + 18 ≤ a
      omega)
  exact hwrstep.trans (hswstep.trans
    (sflushClosedM_getElem g hg a (by omega) hcursor hcount))

/-- Permitted byte mutations of this flush, including nested stack spills.
This describes `__sflush_r`, not the whole native-print call. -/
def SflushWriteFoot (sp : BitVec 64) (a : Nat) : Prop :=
  (sp.toNat - 96 ≤ a ∧ a < sp.toNat) ∨
  (consoleStdout ≤ a ∧ a < consoleStdout + 8) ∨
  (consoleStdout + 12 ≤ a ∧ a < consoleStdout + 16) ∨
  (wrErrnoAddr ≤ a ∧ a < wrErrnoAddr + 4)

theorem SflushFnPost.mem_frame {g : SflushG} {c : Config}
    (h : SflushFnPost g c) (hg : SflushGOk g) :
    AgreeP (fun a => ¬ SflushWriteFoot g.sp a) c.σ.mem g.m0 := by
  intro a ha
  rw [h.mem]
  simp only [SflushWriteFoot, not_or] at ha
  exact sflushCallbackM_getElem g hg a (by omega) (by omega) (by omega) (by omega)

theorem SflushFnPost.buffer_eq {g : SflushG} {c : Config}
    (h : SflushFnPost g c) (hg : SflushGOk g) :
    c.σ.mem[consoleBuf]? = g.m0[consoleBuf]? := by
  rw [h.mem]
  exact ((sflushCallbackM_console_agree g hg consoleBuf
    (Or.inr (Or.inr (Or.inr rfl)))).trans
    (sflushClosedM_buffer g hg)).trans hg.console.bufferByte.symm

#print axioms SflushFnPost.mem_frame
#print axioms SflushFnPost.buffer_eq

end Vsa.Sim

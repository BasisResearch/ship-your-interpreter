import EnvGetSegments
import Vsa.Sim.EnvDefSpec4
import Vsa.Sim.InterpSpillReads
import Vsa.Sim.SegFrameFacts
import Vsa.Sim.Code.Env_get

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

/-- Seven saved words in their actual store order. -/
def prologueLog (sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64) : List WEntry :=
  [((sp0 - 64#64).toNat + 24, 8, r19),
   ((sp0 - 64#64).toNat + 16, 8, r20),
   ((sp0 - 64#64).toNat + 8, 8, r21),
   ((sp0 - 64#64).toNat + 56, 8, r0),
   ((sp0 - 64#64).toNat + 48, 8, r8),
   ((sp0 - 64#64).toNat + 40, 8, r9),
   ((sp0 - 64#64).toNat + 32, 8, r18)]

/-- Normalise only the generated segment's symbolic write log. -/
theorem prologue_log (sp0 env name out r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (h64 : 64 ≤ sp0.toNat) :
    (evalBlocks env_getX2c14Seg (SegEvalState.init
      (env_getX2c14L sp0 r19 r20 r21 r0 r8 r9 r18 env name out) [])).log =
      prologueLog sp0 r0 r8 r9 r18 r19 r20 r21 := by
  change
    [(((sp0 + sign_extend (m := 64) (0xfc0#12)) + sign_extend (m := 64) (0x018#12)).toNat, 8, r19),
     (((sp0 + sign_extend (m := 64) (0xfc0#12)) + sign_extend (m := 64) (0x010#12)).toNat, 8, r20),
     (((sp0 + sign_extend (m := 64) (0xfc0#12)) + sign_extend (m := 64) (0x008#12)).toNat, 8, r21),
     (((sp0 + sign_extend (m := 64) (0xfc0#12)) + sign_extend (m := 64) (0x038#12)).toNat, 8, r0),
     (((sp0 + sign_extend (m := 64) (0xfc0#12)) + sign_extend (m := 64) (0x030#12)).toNat, 8, r8),
     (((sp0 + sign_extend (m := 64) (0xfc0#12)) + sign_extend (m := 64) (0x028#12)).toNat, 8, r9),
     (((sp0 + sign_extend (m := 64) (0xfc0#12)) + sign_extend (m := 64) (0x020#12)).toNat, 8, r18)] = _
  simp only [sp_sub64, BitVec.toNat_add]
  change
    [(((sp0 - 64#64).toNat + 24) % 2^64, 8, r19),
     (((sp0 - 64#64).toNat + 16) % 2^64, 8, r20),
     (((sp0 - 64#64).toNat + 8) % 2^64, 8, r21),
     (((sp0 - 64#64).toNat + 56) % 2^64, 8, r0),
     (((sp0 - 64#64).toNat + 48) % 2^64, 8, r8),
     (((sp0 - 64#64).toNat + 40) % 2^64, 8, r9),
     (((sp0 - 64#64).toNat + 32) % 2^64, 8, r18)] = _
  have hbase := sp_sub64_toNat sp0 h64
  have hlt := sp0.isLt
  simp (disch := omega) only [prologueLog, Nat.mod_eq_of_lt]

/-- Exact words used by the shared restore tail. -/
structure PrologueSaved (m : Mem) (sp r0 r8 r9 r18 r19 r20 r21 : BitVec 64) : Prop where
  ra : read64 m (sp.toNat + 56) = some r0.toNat
  s0 : read64 m (sp.toNat + 48) = some r8.toNat
  s1 : read64 m (sp.toNat + 40) = some r9.toNat
  s2 : read64 m (sp.toNat + 32) = some r18.toNat
  s3 : read64 m (sp.toNat + 24) = some r19.toNat
  s4 : read64 m (sp.toNat + 16) = some r20.toNat
  s5 : read64 m (sp.toNat + 8) = some r21.toNat

theorem prologue_saved (m : Mem) (sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64) :
    PrologueSaved (writeLog m (prologueLog sp0 r0 r8 r9 r18 r19 r20 r21))
      (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21 := by
  let log := prologueLog sp0 r0 r8 r9 r18 r19 r20 r21
  constructor
  · exact read64_of_writeLog_at m log 3 _ _ rfl (by simp [log, prologueLog, OutLRange, Nat.add_assoc])
  · exact read64_of_writeLog_at m log 4 _ _ rfl (by simp [log, prologueLog, OutLRange, Nat.add_assoc])
  · exact read64_of_writeLog_at m log 5 _ _ rfl (by simp [log, prologueLog, OutLRange, Nat.add_assoc])
  · exact read64_of_writeLog_at m log 6 _ _ rfl (by simp [log, prologueLog, OutLRange, Nat.add_assoc])
  · exact read64_of_writeLog_at m log 0 _ _ rfl (by simp [log, prologueLog, OutLRange, Nat.add_assoc])
  · exact read64_of_writeLog_at m log 1 _ _ rfl (by simp [log, prologueLog, OutLRange, Nat.add_assoc])
  · exact read64_of_writeLog_at m log 2 _ _ rfl (by simp [log, prologueLog, OutLRange, Nat.add_assoc])

/-- The seven stores share one stack-window address argument. -/
theorem prologue_store_facts {m : Mem} {L : GRegs} {bs : List (BitVec 8)} {a : MInstr}
    (sp0 : BitVec 64) (off : Nat)
    (hlo : 0x80000000 ≤ sp0.toNat - 64) (hhi : sp0.toNat ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ sp0.toNat - 64) (halign : sp0.toNat % 8 = 0)
    (h64 : 64 ≤ sp0.toNat)
    (hk : a.kind = .sd)
    (hsrc : srcVal a.rs1 L = sp0 + sign_extend (m := 64) (0xfc0#12))
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 64) (hoff8 : off % 8 = 0) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = sp0.toNat - 64 + off := by
    unfold eaddrM
    rw [hsrc, sp_sub64, BitVec.toNat_add, himm, sp_sub64_toNat sp0 h64,
      Nat.mod_eq_of_lt (by omega)]
  apply memFacts_sd_frame m L a bs hk
  all_goals rw [hea]; omega

theorem prologue_facts (m : Mem)
    (sp0 env name out r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (hcode : Code.Env_getLoaded m)
    (hlo : 0x80000000 ≤ sp0.toNat - 64) (hhi : sp0.toNat ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ sp0.toNat - 64) (halign : sp0.toNat % 8 = 0)
    (h64 : 64 ≤ sp0.toNat) :
    ChainFacts m m (env_getX2c14L sp0 r19 r20 r21 r0 r8 r9 r18 env name out) []
      env_getX2c14Seg := by
  chain_facts hcode with "Vsa.Sim.Code.env_get_at_"
  · exact prologue_store_facts sp0 24 hlo hhi hhtif halign h64
      (by decide) (by rfl) (by decide) (by decide) (by decide)
  · exact prologue_store_facts sp0 16 hlo hhi hhtif halign h64
      (by decide) (by rfl) (by decide) (by decide) (by decide)
  · exact prologue_store_facts sp0 8 hlo hhi hhtif halign h64
      (by decide) (by rfl) (by decide) (by decide) (by decide)
  · exact prologue_store_facts sp0 56 hlo hhi hhtif halign h64
      (by decide) (by rfl) (by decide) (by decide) (by decide)
  · exact prologue_store_facts sp0 48 hlo hhi hhtif halign h64
      (by decide) (by rfl) (by decide) (by decide) (by decide)
  · exact prologue_store_facts sp0 40 hlo hhi hhtif halign h64
      (by decide) (by rfl) (by decide) (by decide) (by decide)
  · exact prologue_store_facts sp0 32 hlo hhi hhtif halign h64
      (by decide) (by rfl) (by decide) (by decide) (by decide)

#print axioms prologue_log
#print axioms prologue_saved
#print axioms prologue_store_facts
#print axioms prologue_facts

end Vsa.Sim.EnvGetReflected

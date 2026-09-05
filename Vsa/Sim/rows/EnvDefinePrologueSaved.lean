import Vsa.Sim.rows.EnvDefineEpilogueCore
import Vsa.Sim.EnvDefSpec17

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.MemRepr

namespace Vsa.Sim

/-- The exact prologue image changes only its 64-byte spill window. -/
theorem envDefineSpillMem_outside
    (m : Std.ExtHashMap Nat (BitVec 8)) (sp a : Nat)
    (ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (hout : a < sp ∨ sp + 64 ≤ a) :
    (envDefineSpillMem m sp ra s0 s1 s2 s3 s4 s5 s6)[a]? = m[a]? := by
  unfold envDefineSpillMem
  rw [getElem_writeMap8_disjoint _ sp a _ (by omega),
    getElem_writeMap8_disjoint _ (sp + 40) a _ (by omega),
    getElem_writeMap8_disjoint _ (sp + 48) a _ (by omega),
    getElem_writeMap8_disjoint _ (sp + 56) a _ (by omega),
    getElem_writeMap8_disjoint _ (sp + 8) a _ (by omega),
    getElem_writeMap8_disjoint _ (sp + 16) a _ (by omega),
    getElem_writeMap8_disjoint _ (sp + 32) a _ (by omega),
    getElem_writeMap8_disjoint _ (sp + 24) a _ (by omega)]

/-- Convert the exact prologue write image into the saved-spill carrier. -/
theorem envDefineSavedSpills_of_mem
    {m : Std.ExtHashMap Nat (BitVec 8)} {sp : BitVec 64}
    {saved : (R : Register) → Option (RegisterType R)} {c : Config}
    (ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (hra : saved Register.x1 = some ra) (hs0 : saved Register.x8 = some s0)
    (hs1 : saved Register.x9 = some s1) (hs2 : saved Register.x18 = some s2)
    (hs3 : saved Register.x19 = some s3) (hs4 : saved Register.x20 = some s4)
    (hs5 : saved Register.x21 = some s5) (hs6 : saved Register.x22 = some s6)
    (hmem : c.σ.mem = envDefineSpillMem m sp.toNat ra s0 s1 s2 s3 s4 s5 s6)
    (hcode : Vsa.Sim.Code.Env_defineLoaded c.σ.mem)
    (hlo : 0x80000000 ≤ sp.toNat) (hhi : sp.toNat + 64 ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ sp.toNat) (halign : sp.toNat % 8 = 0)
    (hterm : TermFactsO (runGM envDefineEpilogueBody (envDefineEpilogueL sp)
      [envDefineWordBytes ra, envDefineWordBytes s0, envDefineWordBytes s1,
       envDefineWordBytes s2, envDefineWordBytes s3, envDefineWordBytes s4,
       envDefineWordBytes s5, envDefineWordBytes s6]) envDefineEpilogueTerm) :
    EnvDefineSavedSpillFrame sp saved c := by
  let m1 := writeMap8 m (sp.toNat + 24) (sdData_val s3)
  let m2 := writeMap8 m1 (sp.toNat + 32) (sdData_val s2)
  let m3 := writeMap8 m2 (sp.toNat + 16) (sdData_val s4)
  let m4 := writeMap8 m3 (sp.toNat + 8) (sdData_val s5)
  let m5 := writeMap8 m4 (sp.toNat + 56) (sdData_val ra)
  let m6 := writeMap8 m5 (sp.toNat + 48) (sdData_val s0)
  let m7 := writeMap8 m6 (sp.toNat + 40) (sdData_val s1)
  let m8 := writeMap8 m7 sp.toNat (sdData_val s6)
  have pinNew (mm : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) :
      PinW8 (writeMap8 mm a (sdData_val v)) a v := by
    simpa only [sdData_val_id] using pinw8_of_writeMap mm a (sdData_val v)
  have hm8 : c.σ.mem = m8 := by simpa [envDefineSpillMem, m1, m2, m3, m4, m5, m6, m7, m8] using hmem
  have p24 : PinW8 m8 (sp.toNat + 24) s3 := by
    exact pinw8_survives_writeMap8 sp.toNat _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 40) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 48) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 56) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 8) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 16) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 32) _ (by omega) <|
      pinNew m (sp.toNat + 24) s3
  have p32 : PinW8 m8 (sp.toNat + 32) s2 := by
    exact pinw8_survives_writeMap8 sp.toNat _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 40) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 48) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 56) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 8) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 16) _ (by omega) <|
      pinNew m1 (sp.toNat + 32) s2
  have p16 : PinW8 m8 (sp.toNat + 16) s4 := by
    exact pinw8_survives_writeMap8 sp.toNat _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 40) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 48) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 56) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 8) _ (by omega) <|
      pinNew m2 (sp.toNat + 16) s4
  have p08 : PinW8 m8 (sp.toNat + 8) s5 := by
    exact pinw8_survives_writeMap8 sp.toNat _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 40) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 48) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 56) _ (by omega) <|
      pinNew m3 (sp.toNat + 8) s5
  have p56 : PinW8 m8 (sp.toNat + 56) ra := by
    exact pinw8_survives_writeMap8 sp.toNat _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 40) _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 48) _ (by omega) <|
      pinNew m4 (sp.toNat + 56) ra
  have p48 : PinW8 m8 (sp.toNat + 48) s0 := by
    exact pinw8_survives_writeMap8 sp.toNat _ (by omega) <|
      pinw8_survives_writeMap8 (sp.toNat + 40) _ (by omega) <|
      pinNew m5 (sp.toNat + 48) s0
  have p40 : PinW8 m8 (sp.toNat + 40) s1 := by
    exact pinw8_survives_writeMap8 sp.toNat _ (by omega) <|
      pinNew m6 (sp.toNat + 40) s1
  have p00 : PinW8 m8 sp.toNat s6 := pinNew m7 sp.toNat s6
  apply EnvDefineSavedSpillFrame.of_pinw8 ra s0 s1 s2 s3 s4 s5 s6
      hra hs0 hs1 hs2 hs3 hs4 hs5 hs6 hcode hlo hhi hhtif halign
  all_goals try { rw [hm8]; assumption }
  exact hterm

/-- The existing site-by-site prologue now exposes its exact write image; package
that image as the outer-snapshot spill carrier at the scan dispatch point. -/
theorem env_define_prologue_saved
    (saved : (R : Register) → Option (RegisterType R))
    (sp env name pv r v18 v20 v21 v8 v9 v22 savedS3 vmi : BitVec 64)
    (pn hit count : Nat) (c : Config)
    (hRG : EnvDefRegions sp.toNat env.toNat pv.toNat pn hit count)
    (hG : GoodState c.σ) (hloaded : Vsa.Sim.Code.Env_defineLoaded c.σ.mem)
    (hstrloaded : Vsa.Sim.Code.StrcmpLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80002a5c#64 : BitVec 64))
    (hentry : EnvDefineEntry c.σ sp env name pv r v18 v20 v21 v8 v9 v22)
    (hs3entry : c.σ.regs.get? Register.x19 = some savedS3)
    (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (hread : read32 c.σ.mem env.toNat = some count) (htick : c.tick < 2)
    (hra : saved Register.x1 = some r) (hs0 : saved Register.x8 = some v8)
    (hs1 : saved Register.x9 = some v9) (hs2 : saved Register.x18 = some v18)
    (hs3 : saved Register.x19 = some savedS3)
    (hs4 : saved Register.x20 = some v20) (hs5 : saved Register.x21 = some v21)
    (hs6 : saved Register.x22 = some v22)
    (hterm : TermFactsO (runGM envDefineEpilogueBody (envDefineEpilogueL (sp - 64#64))
      [envDefineWordBytes r, envDefineWordBytes v8, envDefineWordBytes v9,
       envDefineWordBytes v18, envDefineWordBytes savedS3, envDefineWordBytes v20,
       envDefineWordBytes v21, envDefineWordBytes v22]) envDefineEpilogueTerm) :
    ∃ c' vmi', Vsa.Machine.Steps c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002a90#64 : BitVec 64) ∧
      EnvDefinePrologueReady c'.σ sp env name pv ∧
      c'.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 count) ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧ GoodState c'.σ ∧
      Vsa.Sim.Code.Env_defineLoaded c'.σ.mem ∧ Vsa.Sim.Code.StrcmpLoaded c'.σ.mem ∧
      EnvDefineSavedSpillFrame (sp - 64#64) saved c' ∧ c'.tick < 2 ∧
      (∀ a, ¬ ((sp - 64#64).toNat ≤ a ∧ a < (sp - 64#64).toNat + 64) →
        c'.σ.mem[a]? = c.σ.mem[a]?) := by
  obtain ⟨c', vmi', hsteps, hpc', hready, hcount, hmi', hG', hloaded', hstrcmp',
      hmem', htick'⟩ :=
    env_define_prologue sp env name pv r v18 v20 v21 v8 v9 v22 savedS3 vmi
      pn hit count c hRG hG hloaded hstrloaded hpc hentry hs3entry hmi hread htick
  have hbase : (sp - 64#64).toNat = sp.toNat - 64 := sp_sub64_toNat sp hRG.sp_ge
  have hsaved : EnvDefineSavedSpillFrame (sp - 64#64) saved c' := by
    apply envDefineSavedSpills_of_mem r v8 v9 v18 savedS3 v20 v21 v22
      hra hs0 hs1 hs2 hs3 hs4 hs5 hs6 hmem' hloaded'
    · rw [hbase]; exact hRG.frame_lo
    · rw [hbase]
      have hhi := hRG.frame_hi
      omega
    · rw [hbase]; exact hRG.frame_win
    · rw [hbase]
      have h16 := hRG.frame_align
      omega
    · exact hterm
  refine ⟨c', vmi', hsteps, hpc', hready, hcount, hmi', hG', hloaded', hstrcmp',
    hsaved, htick', ?_⟩
  intro a ha
  rw [hmem']
  exact envDefineSpillMem_outside c.σ.mem (sp - 64#64).toNat a
    r v8 v9 v18 savedS3 v20 v21 v22 (by omega)

#print axioms envDefineSavedSpills_of_mem
#print axioms envDefineSpillMem_outside
#print axioms env_define_prologue_saved

end Vsa.Sim

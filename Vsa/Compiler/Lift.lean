import Vsa.Compiler.Machine

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Vsa.Machine (MState Config Step Steps Halted Halts output)

abbrev ReachCorr (c : Config) (A : AM) : Prop := ∃ c', Steps c c' ∧ Corr c' A

abbrev StepsCorr (c : Config) (A : AM) : Prop := ∃ c', Steps c c' ∧ c.steps < c'.steps ∧ Corr c' A

abbrev Step1Corr (c : Config) (A : AM) : Prop := ∃ c', Steps c c' ∧ c'.steps = c.steps + 1 ∧ Corr c' A

theorem Step1Corr.toSC {c : Config} {A : AM} (h : Step1Corr c A) : StepsCorr c A :=
  let ⟨c', hs, he, hc⟩ := h; ⟨c', hs, by omega, hc⟩

theorem applyW8_low (m : Mem) (ea : Nat) (v : BitVec 64) (j : Nat) (hj : j < ea) :
    (applyW m (ea, 8, v))[j]? = m[j]? := writeMap8_low_miss m ea _ j hj

theorem htifOut_mem {v : BitVec 64} {A A' : AM} (h : htifOut v A = some (.run A')) :
    A'.mem = A.mem := by
  unfold htifOut at h
  split at h; · cases h
  split at h; · cases h
  split at h
  · cases h; rfl
  · cases h

theorem libCall_mem {t : Nat} {A A' : AM} (h : libCall t A = some (.run A')) :
    A'.mem = A.mem := by
  unfold libCall at h
  split at h
  · split at h
    · split at h
      · cases h; rfl
      · split at h
        · cases h; rfl
        · split at h
          · cases h; rfl
          · cases h
    · cases h
  · cases h

theorem astep_mem_low {code : List Ins} {A A' : AM} (h : astep code A = some (.run A')) :
    ∀ j, j < tohostAddr + 16 → A'.mem[j]? = A.mem[j]? := by
  intro j hj
  unfold astep at h
  split at h
  · rename_i i _
    cases i <;> simp only [exec] at h <;> (repeat' split at h) <;>
      first
      | (cases h; rfl)
      | (cases h; done)
      | exact congrArg (·[j]?) (htifOut_mem h)
      | exact congrArg (·[j]?) (libCall_mem h)
      | (cases h; exact applyW8_low _ _ _ _ (by omega))
  · cases h

theorem CodeAt.of_low {m m' : Mem} {code : List Ins}
    (hlen : codeBase + 4 * code.length ≤ tohostAddr)
    (hagree : ∀ j, j < tohostAddr + 16 → m'[j]? = m[j]?) (h : CodeAt m code) :
    CodeAt m' code := by
  intro k i hk j hj
  have hk' : k < code.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [hagree _ (by omega)]
  exact h k i hk j hj

theorem LibLoaded.of_low {m m' : Mem}
    (hagree : ∀ j, j < tohostAddr + 16 → m'[j]? = m[j]?) (h : LibLoaded m) :
    LibLoaded m' := by
  have hag : ∀ j, j < tohostAddr → m'[j]? = m[j]? := fun j hj => hagree j (by omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Code.__muldi3Loaded, Code.__muldi3Chunk0, Code.__divdi3Loaded,
      Code.__divdi3Chunk0, Code.__umoddi3Loaded, Code.__umoddi3Chunk0,
      Code.__hidden___udivdi3Loaded, Code.__hidden___udivdi3Chunk0, Code.__hidden___udivdi3Chunk1,
      Code.__moddi3Loaded, Code.__moddi3Chunk0] at h1 h2 h3 h4 h5 ⊢
    simp (disch := (simp only [tohostAddr]; decide)) only [hag]
    assumption

theorem toM_fields (i : Ins) (hi : i.IsM) (pc : BitVec 64) :
    (i.toM pc).pc = pc ∧ (i.toM pc).word = i.encode ∧ (i.toM pc).b0 = byte i.encode 0 ∧
      (i.toM pc).b1 = byte i.encode 1 ∧ (i.toM pc).b2 = byte i.encode 2 ∧
      (i.toM pc).b3 = byte i.encode 3 := by
  cases i <;> first | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | exact hi.elim

theorem gprReg_ne_pw (n : Nat) : (gprReg n == Register.htif_payload_writes) = false := by
  unfold gprReg; split <;> decide

theorem keys_stepGM (a : MInstr) (L : GRegs) (bs : List (BitVec 8))
    (hrd : a.kind = .sd ∨ (1 ≤ a.rd ∧ a.rd ≤ 31)) (hK : KeysOK (keysG L)) :
    KeysOK (keysG (stepGM a L bs)) := by
  unfold stepGM
  split
  · exact hK
  · exact hK
  · exact hK
  · exact hK
  · rename_i hk1 hk2 hk3 hk4
    have hrd' : 1 ≤ a.rd ∧ a.rd ≤ 31 := by
      rcases hrd with h | h
      · exact absurd h hk2
      · exact h
    intro n hn
    cases hn with
    | head => exact hrd'
    | tail _ h => exact hK n (mem_of_mem_keysG_eraseG L h)

theorem writeLog_one (m : Mem) (a : MInstr) (L : GRegs) (lds : List (List (BitVec 8))) :
    writeLog m (wlogM [a] L lds) = stepMemM m a L := by
  unfold wlogM stepMemM
  split <;> simp [wlogM, writeLog]

theorem sim_M (i : Ins) (hi : i.IsM) {A : AM} {c : Config} (hc : Corr c A)
    (hb : ∀ j < 4, A.mem[A.pc.toNat + j]? = some (byte i.encode j))
    (hlo : 0x80000000 ≤ A.pc.toNat) (hhi : A.pc.toNat + 4 ≤ tohostAddr)
    (hal : A.pc.toNat % 4 = 0)
    (hk : KindOK (keysG A.regs) (i.toM A.pc).kind (i.toM A.pc).rd (i.toM A.pc).rs1
      (i.toM A.pc).rs2)
    (bs : List (BitVec 8)) (hmf : MemFacts A.mem A.regs bs (i.toM A.pc))
    (hrd : (i.toM A.pc).kind = .sd ∨ (1 ≤ (i.toM A.pc).rd ∧ (i.toM A.pc).rd ≤ 31)) :
    Step1Corr c ⟨BitVec.addInt A.pc 4, stepGM (i.toM A.pc) A.regs bs,
        stepMemM A.mem (i.toM A.pc) A.regs, A.out⟩ := by
  obtain ⟨σ, t, u⟩ := c
  obtain ⟨vm, hvm⟩ := hc.good.minstret
  obtain ⟨fpc, fw, f0, f1, f2, f3⟩ := toM_fields i hi A.pc
  have hmem : σ.mem = A.mem := hc.mem
  have hbp : BytePinsM σ.mem (i.toM A.pc) := by
    unfold BytePinsM; rw [fpc, f0, f1, f2, f3, hmem]
    exact ⟨by simpa using hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega)⟩
  have hok : InstrOKM A.pc (keysG A.regs) (i.toM A.pc) := by
    refine ⟨by rw [fpc], ?_, ?_, by rw [fpc]; exact hlo, by rw [fpc]; exact hhi,
      by rw [fpc]; exact hal, hk⟩
    · rw [f0, f1, f2, f3, fw, bytes_word]
    · rw [f0, f1, f2, f3, bytes_word, encode_rvc]
  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', _, hL', hfr⟩ :=
    block_mem_run [i.toM A.pc] σ t u A.pc vm A.regs [bs] σ.mem σ.mem (keysG A.regs)
      hc.good hc.pc hvm rfl (fun _ _ => rfl) hc.regs hc.keys (fun _ h => h)
      ⟨hbp, decodeFactM_toM A.pc i hi, hmem ▸ hmf, trivial⟩ ⟨hok, trivial⟩ hc.tick
  refine ⟨⟨σ', i', u + 1⟩, hs, by simp, ?_⟩
  refine ⟨hG', hi', ?_, hL', keys_stepGM _ _ _ hrd hc.keys, ?_, hout'.trans hc.out, ?_⟩
  · rw [hpc']; simp only [endPCM, fpc]
  · rw [hmem', writeLog_one, hmem]
  · rw [hfr _ (by decide) (fun n _ => gprReg_ne_pw n)]
    exact hc.pw

theorem toT_fields (i : Ins) (pc : BitVec 64) (tk : Bool) :
    (i.toT pc tk).pc = pc ∧ (i.toT pc tk).word = i.encode ∧ (i.toT pc tk).b0 = byte i.encode 0 ∧
      (i.toT pc tk).b1 = byte i.encode 1 ∧ (i.toT pc tk).b2 = byte i.encode 2 ∧
      (i.toT pc tk).b3 = byte i.encode 3 := by
  cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sim_T (i : Ins) (hi : i.IsT) (tk : Bool) {A : AM} {c : Config} (hc : Corr c A)
    (hb : ∀ j < 4, A.mem[A.pc.toNat + j]? = some (byte i.encode j))
    (hlo : 0x80000000 ≤ A.pc.toNat) (hhi : A.pc.toNat + 4 ≤ tohostAddr)
    (hal : A.pc.toNat % 4 = 0)
    (hk : TermKindOK (keysG A.regs) A.pc (i.toT A.pc tk).rs1 (i.toT A.pc tk).rs2
      (i.toT A.pc tk).imm13 (i.toT A.pc tk).imm21 (i.toT A.pc tk).kind)
    (htf : TermFactsT A.regs (i.toT A.pc tk)) :
    Step1Corr c { A with pc := tgtPCT (i.toT A.pc tk) A.regs } := by
  obtain ⟨σ, t, u⟩ := c
  obtain ⟨vm, hvm⟩ := hc.good.minstret
  obtain ⟨fpc, fw, f0, f1, f2, f3⟩ := toT_fields i A.pc tk
  have hmem : σ.mem = A.mem := hc.mem
  have hwf : TermWF (keysG A.regs) (i.toT A.pc tk) := by
    refine ⟨?_, ?_, by rw [fpc]; exact hlo, by rw [fpc]; exact hhi, by rw [fpc]; exact hal,
      by rw [fpc]; exact hk⟩
    · rw [f0, f1, f2, f3, fw, bytes_word]
    · rw [f0, f1, f2, f3, bytes_word, encode_rvc]
  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', _, hL', hfr⟩ :=
    term_step_bt (i.toT A.pc tk) σ t u vm A.regs (keysG A.regs) hc.good (by rw [fpc]; exact hc.pc) hvm
      hc.regs hc.keys (fun _ h => h)
      (by rw [fpc, f0, hmem]; simpa using hb 0 (by omega))
      (by rw [fpc, f1, hmem]; exact hb 1 (by omega))
      (by rw [fpc, f2, hmem]; exact hb 2 (by omega))
      (by rw [fpc, f3, hmem]; exact hb 3 (by omega))
      (decodeFactT_toT A.pc tk i hi) hwf htf hc.tick
  refine ⟨⟨σ', i', u + 1⟩, .single hs, by simp, ?_⟩
  exact ⟨hG', hi', hpc', hL', hc.keys, hmem'.trans hmem, hout'.trans hc.out,
    (hfr _ (by decide)).trans hc.pw⟩

theorem gprGet_congr {σ σ' : MState} :
    ∀ n, 1 ≤ n → n ≤ 31 → σ'.regs.get? (gprReg n) = σ.regs.get? (gprReg n) →
      gprGet σ' n = gprGet σ n
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, _, h => h
  | 2, _, _, h => h
  | 3, _, _, h => h
  | 4, _, _, h => h
  | 5, _, _, h => h
  | 6, _, _, h => h
  | 7, _, _, h => h
  | 8, _, _, h => h
  | 9, _, _, h => h
  | 10, _, _, h => h
  | 11, _, _, h => h
  | 12, _, _, h => h
  | 13, _, _, h => h
  | 14, _, _, h => h
  | 15, _, _, h => h
  | 16, _, _, h => h
  | 17, _, _, h => h
  | 18, _, _, h => h
  | 19, _, _, h => h
  | 20, _, _, h => h
  | 21, _, _, h => h
  | 22, _, _, h => h
  | 23, _, _, h => h
  | 24, _, _, h => h
  | 25, _, _, h => h
  | 26, _, _, h => h
  | 27, _, _, h => h
  | 28, _, _, h => h
  | 29, _, _, h => h
  | 30, _, _, h => h
  | 31, _, _, h => h
  | _ + 32, _, h, _ => absurd h (by omega)

theorem gholds_iff (σ : MState) : ∀ L : GRegs, GHolds σ L ↔ ∀ p ∈ L, gprGet σ p.1 = some p.2
  | [] => by simp [GHolds]
  | (n, v) :: L => by
    simp only [GHolds, List.mem_cons, forall_eq_or_imp, gholds_iff σ L]

theorem mem_keysG {p : Nat × BitVec 64} : ∀ {L : GRegs}, p ∈ L → p.1 ∈ keysG L
  | (n, v) :: L, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_keysG h)

theorem mem_eraseG {p : Nat × BitVec 64} {n : Nat} :
    ∀ {L : GRegs}, p ∈ eraseG n L → p ∈ L ∧ p.1 ≠ n
  | [], h => nomatch h
  | (m, w) :: L, h => by
    simp only [eraseG] at h
    split at h
    · have := mem_eraseG h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · rename_i hne
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨List.mem_cons_self .., hne⟩
      · have := mem_eraseG h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem mem_eraseAll {p : Nat × BitVec 64} :
    ∀ {S : List Nat} {L : GRegs}, p ∈ eraseAll S L → p ∈ L ∧ p.1 ∉ S
  | [], L, h => ⟨h, by simp⟩
  | n :: S, L, h => by
    have h' := mem_eraseAll (S := S) (L := eraseG n L) h
    have h'' := mem_eraseG h'.1
    refine ⟨h''.1, ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨h''.2, h'.2⟩

theorem keysG_mem {k : Nat} : ∀ {L : GRegs}, k ∈ keysG L → ∃ v, (k, v) ∈ L
  | (n, v) :: L, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨v, List.mem_cons_self ..⟩
    · obtain ⟨w, hw⟩ := keysG_mem h; exact ⟨w, List.mem_cons_of_mem _ hw⟩

theorem keysOK_eraseAll {S : List Nat} {L : GRegs} (h : KeysOK (keysG L)) :
    KeysOK (keysG (eraseAll S L)) := by
  intro k hk
  obtain ⟨v, hv⟩ := keysG_mem hk
  exact h k (mem_keysG (mem_eraseAll hv).1)

theorem gholds_eraseAll {σ σ' : MState} {S : List Nat} {L : GRegs}
    (hK : KeysOK (keysG L)) (hL : GHolds σ L)
    (h : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ S → gprGet σ' n = gprGet σ n) :
    GHolds σ' (eraseAll S L) := by
  rw [gholds_iff] at hL ⊢
  intro p hp
  obtain ⟨hpL, hpS⟩ := mem_eraseAll hp
  have hk := hK p.1 (mem_keysG hpL)
  rw [h p.1 hk.1 hk.2 hpS]
  exact hL p hpL

structure NonGpr (R : Register) : Prop where
  minstret : (Register.minstret == R) = false
  pc : (Register.PC == R) = false
  nextPC : (Register.nextPC == R) = false
  inc : (Register.minstret_increment == R) = false
  mcycle : (Register.mcycle == R) = false
  mtime : (Register.mtime == R) = false
  mip : (Register.mip == R) = false
  cmd : (Register.htif_cmd_write == R) = false
  pw : (Register.htif_payload_writes == R) = false
  tohost : (Register.htif_tohost == R) = false

theorem nonGpr (n : Nat) : NonGpr (gprReg n) := by
  unfold gprReg; split <;> exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem gprReg_ne_x1 : ∀ n, n < 32 → 1 ≤ n → n ≠ 1 → (Register.x1 == gprReg n) = false := by
  decide

theorem sim_jal_link (off : BitVec 21) {A : AM} {c : Config} (hc : Corr c A)
    (hb : ∀ j < 4, A.mem[A.pc.toNat + j]? = some (byte (Ins.jal 1 off).encode j))
    (hlo : 0x80000000 ≤ A.pc.toNat) (hhi : A.pc.toNat + 4 ≤ tohostAddr)
    (hal : A.pc.toNat % 4 = 0)
    (htgt : (A.pc + sign_extend (m := 64) (evenJ off)).toNat % 4 = 0) :
    Step1Corr c (AM.mk (A.pc + sign_extend (m := 64) (evenJ off))
        ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) A.mem A.out) := by
  obtain ⟨σ, t, u⟩ := c
  obtain ⟨vm, hvm⟩ := hc.good.minstret
  have hmem : σ.mem = A.mem := hc.mem
  have hG := hc.good
  have hdec := decode_jal_link (afterPrelude σ)
    ⟨by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa,
     by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege,
     by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg⟩ 1 off
  obtain ⟨-, -, -, -, r5⟩ := gpr_rd_ok 1 (by omega) (by omega)
  obtain ⟨σ', i', hs, hi', hG', hmem', hobs⟩ :=
    stepObs_exec (u := u) (A.pc + sign_extend (m := 64) (evenJ off)) vm
      (Fetched.of_bytes hG hc.pc (by rw [hmem]; simpa using hb 0 (by omega))
        (by rw [hmem]; exact hb 1 (by omega)) (by rw [hmem]; exact hb 2 (by omega))
        (by rw [hmem]; exact hb 3 (by omega)) hlo hhi hal (by rw [bytes_word, encode_rvc])
        (bytes_word _) hdec)
      (execute_jal_char (evenJ off) (gprIdx 1) _ A.pc _ _ _ (by reg_reads []) (by reg_reads [hc.pc])
        (by reg_reads [hG.misa]) htgt (wX_bits_gpr _ _ 1 (by decide) (by decide)))
      (((RetireReads.prelude hG hvm _).jump _).write _)
      (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned r5 _) hc.tick
  have hrd : ∀ R : Register, (Register.minstret == R) = false → (Register.PC == R) = false →
      (Register.x1 == R) = false → (Register.nextPC == R) = false →
      (Register.minstret_increment == R) = false → (Register.mcycle == R) = false →
      (Register.mtime == R) = false → (Register.mip == R) = false →
      σ'.regs.get? R = σ.regs.get? R := by
    intro R h1 h2 h3 h4 h5 h6 h7 h8
    rw [hobs.1 R h6 h7 h8]
    exact get?_sigmaPost_jal σ A.pc vm (evenJ off) Register.x1 _ R h1 h2 h3 h4 h5
  refine ⟨⟨σ', i', u + 1⟩, .single hs, by simp, hG', hi', ?_, ?_, ?_, hmem'.trans hmem,
    (hobs.2.trans (sailOutput_sigmaPost_jal _ _ _ _ _ _)).trans hc.out, ?_⟩
  · rw [hobs.1 _ (by decide) (by decide) (by decide)]
    show ((((sigma3_jal σ A.pc (evenJ off) Register.x1 _).regs.insert Register.PC _).insert
      Register.minstret _)).get? Register.PC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg,
      reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]
  · refine ⟨?_, ?_⟩
    · show σ'.regs.get? Register.x1 = _
      rw [hobs.1 _ (by decide) (by decide) (by decide)]
      show ((((sigma3_jal σ A.pc (evenJ off) Register.x1 _).regs.insert Register.PC _).insert
        Register.minstret _)).get? Register.x1 = _
      rw [Std.ExtDHashMap.get?_insert]
      simp only [show (Register.minstret == Register.x1) = false from by decide, dif_neg,
        reduceCtorEq, not_false_eq_true]
      rw [Std.ExtDHashMap.get?_insert]
      simp only [show (Register.PC == Register.x1) = false from by decide, dif_neg,
        reduceCtorEq, not_false_eq_true]
      show (((afterNextPC (afterPrelude σ) A.pc).regs.insert Register.nextPC _).insert
        Register.x1 _).get? Register.x1 = _
      rw [Std.ExtDHashMap.get?_insert_self]; rfl
    · exact gholds_eraseAll (S := [1]) hc.keys hc.regs fun n h1 h31 hn =>
        gprGet_congr n h1 h31 (hrd _ (nonGpr n).minstret (nonGpr n).pc
          (gprReg_ne_x1 n (by omega) h1 (by simpa using hn)) (nonGpr n).nextPC
          (nonGpr n).inc (nonGpr n).mcycle (nonGpr n).mtime (nonGpr n).mip)
  · intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨by omega, by omega⟩
    · exact hc.keys k (mem_of_mem_keysG_eraseG _ hk)
  · rw [hrd _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hc.pw

theorem nw_gpr (n : Nat) (h1 : 1 ≤ n) (h31 : n ≤ 31) (hn : n ∉ clobbered) :
    NotWrittenD (gprReg n) := by
  simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨n1, n5, n10, n11, n12, n13⟩ := hn
  have ng := nonGpr n
  exact ⟨⟨gprReg_beq_false 10 (by omega) n (by omega) (by omega) h1 (Ne.symm n10),
    gprReg_beq_false 11 (by omega) n (by omega) (by omega) h1 (Ne.symm n11),
    gprReg_beq_false 12 (by omega) n (by omega) (by omega) h1 (Ne.symm n12),
    gprReg_beq_false 13 (by omega) n (by omega) (by omega) h1 (Ne.symm n13),
    ng.pc, ng.nextPC, ng.minstret, ng.inc, ng.mcycle, ng.mtime, ng.mip⟩,
    gprReg_beq_false 1 (by omega) n (by omega) (by omega) h1 (Ne.symm n1),
    gprReg_beq_false 5 (by omega) n (by omega) (by omega) h1 (Ne.symm n5)⟩

theorem corr_after_lib {c1 c' : Config} {A1 : AM} {r res : BitVec 64} (hc : Corr c1 A1)
    (hG : GoodState c'.σ) (ht : c'.tick < 2) (hmem : c'.σ.mem = c1.σ.mem)
    (hout : c'.σ.sailOutput = c1.σ.sailOutput)
    (hpc : c'.σ.regs.get? Register.PC = some r) (h10 : c'.σ.regs.get? Register.x10 = some res)
    (hfr : ∀ R, NotWrittenD R → c'.σ.regs.get? R = c1.σ.regs.get? R) :
    Corr c' ⟨r, (10, res) :: eraseAll clobbered A1.regs, A1.mem, A1.out⟩ := by
  refine ⟨hG, ht, hpc, ⟨h10, ?_⟩, ?_, hmem.trans hc.mem, hout.trans hc.out, ?_⟩
  · exact gholds_eraseAll hc.keys hc.regs fun n h1 h31 hn =>
      gprGet_congr n h1 h31 (hfr _ (nw_gpr n h1 h31 hn))
  · intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨by omega, by omega⟩
    · exact keysOK_eraseAll hc.keys k hk
  · rw [hfr _ ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩, by decide, by decide⟩]
    exact hc.pw

theorem corr_reg {c : Config} {A : AM} (hc : Corr c A) {n : Nat} {v : BitVec 64}
    (h : lookupG n A.regs = some v) : gprGet c.σ n = some v :=
  gholds_lookup A.regs hc.regs h

theorem corr_reg_ex {c : Config} {A : AM} (hc : Corr c A) {n : Nat} (h : n ∈ keysG A.regs) :
    ∃ v, gprGet c.σ n = some v := by
  obtain ⟨v, hv⟩ := lookup_of_mem A.regs h
  exact ⟨v, corr_reg hc hv⟩

theorem sim_mul {A : AM} {c : Config} (hc : Corr c A) (hpc : A.pc = 0x80004640#64)
    {r x y : BitVec 64} (hr : lookupG 1 A.regs = some r) (hral : r.toNat % 4 = 0)
    (hx : lookupG 10 A.regs = some x) (hy : lookupG 11 A.regs = some y)
    (h12 : 12 ∈ keysG A.regs) (h13 : 13 ∈ keysG A.regs) (hlib : LibLoaded A.mem) :
    ReachCorr c ⟨r, (10, x * y) :: eraseAll clobbered A.regs, A.mem, A.out⟩ := by
  obtain ⟨v12, h12'⟩ := corr_reg_ex hc h12
  obtain ⟨v13, h13'⟩ := corr_reg_ex hc h13
  obtain ⟨c', hs, hG, hmem, hout, hpc', h10, _, ht, hfr⟩ :=
    muldi3_spec (fun R => c.σ.regs.get? R) x y r c.σ.mem c.σ.sailOutput c
      ⟨⟨v12, v13, ⟨hc.good, hc.mem ▸ hlib.mul, rfl, rfl, hpc ▸ hc.pc, corr_reg hc hx,
        corr_reg hc hy, h12', h13', corr_reg hc hr, hc.good.minstret, hc.tick,
        fun _ _ => rfl⟩⟩, hral⟩
  exact ⟨c', hs, corr_after_lib hc hG ht hmem hout hpc' h10 (fun R h => hfr R h.1)⟩

theorem sim_div {A : AM} {c : Config} (hc : Corr c A) (hpc : A.pc = 0x800046a4#64)
    {r x y : BitVec 64} (hr : lookupG 1 A.regs = some r) (hral : r.toNat % 4 = 0)
    (hx : lookupG 10 A.regs = some x) (hy : lookupG 11 A.regs = some y) (hy0 : y.toInt ≠ 0)
    (h12 : 12 ∈ keysG A.regs) (h13 : 13 ∈ keysG A.regs) (hlib : LibLoaded A.mem) :
    ReachCorr c ⟨r, (10, BitVec.ofInt 64 (x.toInt.tdiv y.toInt)) ::
      eraseAll clobbered A.regs, A.mem, A.out⟩ := by
  obtain ⟨c', hs, post⟩ :=
    divdi3_wrap_spec (fun R => c.σ.regs.get? R) x y r c.σ.mem c.σ.sailOutput c
      ⟨hc.good, hc.mem ▸ hlib.div, hc.mem ▸ hlib.umod, hc.mem ▸ hlib.udiv, rfl, rfl,
        hpc ▸ hc.pc, corr_reg hc hx, corr_reg hc hy, corr_reg hc hr, hc.good.minstret,
        corr_reg_ex hc h12, corr_reg_ex hc h13, hc.tick, hy0, hral, fun _ _ => rfl⟩
  exact ⟨c', hs, corr_after_lib hc post.good post.tick post.mem post.output post.pc
    post.quotient post.frame⟩

theorem sim_mod {A : AM} {c : Config} (hc : Corr c A) (hpc : A.pc = 0x80004728#64)
    {r x y : BitVec 64} (hr : lookupG 1 A.regs = some r) (hral : r.toNat % 4 = 0)
    (hx : lookupG 10 A.regs = some x) (hy : lookupG 11 A.regs = some y) (hy0 : y.toInt ≠ 0)
    (h12 : 12 ∈ keysG A.regs) (h13 : 13 ∈ keysG A.regs) (hlib : LibLoaded A.mem) :
    ReachCorr c ⟨r, (10, BitVec.ofInt 64 (x.toInt.tmod y.toInt)) ::
      eraseAll clobbered A.regs, A.mem, A.out⟩ := by
  obtain ⟨c', hs, hG, hmem, hout, hpc', ht, hfr, res, h10, hres⟩ :=
    moddi3_spec (fun R => c.σ.regs.get? R) x y r c.σ.mem c.σ.sailOutput c
      ⟨hc.good, hc.mem ▸ hlib.mod, hc.mem ▸ hlib.udiv, rfl, rfl, hpc ▸ hc.pc,
        corr_reg hc hx, corr_reg hc hy, corr_reg hc hr, hc.good.minstret,
        corr_reg_ex hc h12, corr_reg_ex hc h13, hc.tick, hy0, hral, fun _ _ => rfl⟩
  have hres' : BitVec.ofInt 64 (x.toInt.tmod y.toInt) = res := by
    rw [← hres, BitVec.ofInt_toInt]
  exact ⟨c', hs, corr_after_lib hc hG ht hmem hout hpc' (hres' ▸ h10) hfr⟩

theorem sext12_zero : sign_extend (m := 64) (0#12) = 0#64 := by decide

theorem sd_tohost_facts {A : AM} {c : Config} (hc : Corr c A) (rs2 rs1 : Nat)
    (h1 : SrcOK rs1 (keysG A.regs)) (h2 : SrcOK rs2 (keysG A.regs))
    (hea : (srcVal rs1 A.regs).toNat = tohostAddr) :
    (ext_decode (Ins.sd rs2 rs1).encode).run (afterPrelude c.σ)
        = .ok (instruction.STORE (0#12, gprIdx rs2, gprIdx rs1, 8)) (afterPrelude c.σ) ∧
      (rX_bits (gprIdx rs1)).run (afterNextPC (afterPrelude c.σ) A.pc)
        = .ok (srcVal rs1 A.regs) (afterNextPC (afterPrelude c.σ) A.pc) ∧
      (rX_bits (gprIdx rs2)).run (afterNextPC (afterPrelude c.σ) A.pc)
        = .ok (srcVal rs2 A.regs) (afterNextPC (afterPrelude c.σ) A.pc) ∧
      srcVal rs1 A.regs + sign_extend (m := 64) (0#12) = BitVec.ofNat 64 tohostAddr := by
  have hG := hc.good
  refine ⟨decodeFactM_toM A.pc (.sd rs2 rs1) trivial (afterPrelude c.σ)
      (by rw [get?_afterPrelude _ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude _ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude _ _ (by decide)]; exact hG.mseccfg),
    rX_src c.σ A.pc rs1 h1.1 _ (srcPin_srcVal c.σ A.regs rs1 h1.2 hc.regs),
    rX_src c.σ A.pc rs2 h2.1 _ (srcPin_srcVal c.σ A.regs rs2 h2.2 hc.regs), ?_⟩
  rw [sext12_zero, BitVec.add_zero]
  apply BitVec.eq_of_toNat_eq
  rw [hea]; simp [tohostAddr]

theorem sim_putc {A : AM} {c : Config} (hc : Corr c A) (rs2 rs1 : Nat)
    (hb : ∀ j < 4, A.mem[A.pc.toNat + j]? = some (byte (Ins.sd rs2 rs1).encode j))
    (hlo : 0x80000000 ≤ A.pc.toNat) (hhi : A.pc.toNat + 4 ≤ tohostAddr)
    (hal : A.pc.toNat % 4 = 0)
    (h1 : SrcOK rs1 (keysG A.regs)) (h2 : SrcOK rs2 (keysG A.regs))
    (hea : (srcVal rs1 A.regs).toNat = tohostAddr)
    (hv : srcVal rs2 A.regs = putcWord ((srcVal rs2 A.regs).setWidth 8)) :
    Step1Corr c (AM.mk (BitVec.addInt A.pc 4) A.regs A.mem
        (A.out.push (toString (Char.ofNat ((srcVal rs2 A.regs).setWidth 8).toNat)))) := by
  obtain ⟨hdec, hrs1, hrs2, haddr⟩ := sd_tohost_facts hc rs2 rs1 h1 h2 hea
  obtain ⟨σ, t, u⟩ := c
  obtain ⟨vm, hvm⟩ := hc.good.minstret
  obtain ⟨th, hth⟩ := hc.good.htif_tohost
  have hmem : σ.mem = A.mem := hc.mem
  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', _, hpw', _, hfr⟩ :=
    stepObs_tohost_putchar σ t u A.pc vm (Ins.sd rs2 rs1).encode 0#12 (gprIdx rs2) (gprIdx rs1)
      _ _ _ ((srcVal rs2 A.regs).setWidth 8) th _ _ _ _ hc.good hc.pc hvm (bytes_word _)
      (by rw [bytes_word, encode_rvc]) hdec hrs1 hrs2 haddr rfl hc.pw hth hv
      (by rw [hmem]; simpa using hb 0 (by omega)) (by rw [hmem]; exact hb 1 (by omega))
      (by rw [hmem]; exact hb 2 (by omega)) (by rw [hmem]; exact hb 3 (by omega))
      hlo hhi hal hc.tick
  refine ⟨⟨σ', i', u + 1⟩, .single hs, by simp, hG', hi', hpc', ?_, hc.keys,
    hmem'.trans hmem, by rw [hout', hc.out], hpw'⟩
  have hL := hc.regs
  have hK := hc.keys
  rw [gholds_iff] at hL ⊢
  intro p hp
  have hk := hK p.1 (mem_keysG hp)
  rw [gprGet_congr p.1 hk.1 hk.2 (hfr _ (nonGpr _).pc (nonGpr _).minstret (nonGpr _).inc
    (nonGpr _).nextPC (nonGpr _).cmd (nonGpr _).pw (nonGpr _).tohost (nonGpr _).mip
    (nonGpr _).mtime (nonGpr _).mcycle)]
  exact hL p hp

theorem sim_exit (e : BitVec 64) (he : e.toNat < 2 ^ 47) {A : AM} {c : Config} (hc : Corr c A)
    (rs2 rs1 : Nat)
    (hb : ∀ j < 4, A.mem[A.pc.toNat + j]? = some (byte (Ins.sd rs2 rs1).encode j))
    (hlo : 0x80000000 ≤ A.pc.toNat) (hhi : A.pc.toNat + 4 ≤ tohostAddr)
    (hal : A.pc.toNat % 4 = 0)
    (h1 : SrcOK rs1 (keysG A.regs)) (h2 : SrcOK rs2 (keysG A.regs))
    (hea : (srcVal rs1 A.regs).toNat = tohostAddr)
    (hv : srcVal rs2 A.regs = exitWord e) :
    ∃ σf, Halted c e.toNat σf ∧ output σf = String.join A.out.toList := by
  obtain ⟨hdec, hrs1, hrs2, haddr⟩ := sd_tohost_facts hc rs2 rs1 h1 h2 hea
  obtain ⟨σ, t, u⟩ := c
  obtain ⟨vm, hvm⟩ := hc.good.minstret
  obtain ⟨th, hth⟩ := hc.good.htif_tohost
  have hmem : σ.mem = A.mem := hc.mem
  have hst := stepOnce_tohost_exitE e he σ t u A.pc vm (Ins.sd rs2 rs1).encode 0#12
    (gprIdx rs2) (gprIdx rs1) _ _ _ th _ _ _ _ hc.good hc.pc hvm (bytes_word _)
    (by rw [bytes_word, encode_rvc]) hdec hrs1 hrs2 haddr rfl hc.pw hth hv
    (by rw [hmem]; simpa using hb 0 (by omega)) (by rw [hmem]; exact hb 1 (by omega))
    (by rw [hmem]; exact hb 2 (by omega)) (by rw [hmem]; exact hb 3 (by omega))
    hlo hhi hal
  refine ⟨_, Halted.mk hst, ?_⟩
  simp only [output]
  rw [show σ.sailOutput = A.out from hc.out]

theorem addInt4_toNat (pc : BitVec 64) (h : pc.toNat + 4 < 2 ^ 64) :
    (BitVec.addInt pc 4).toNat = pc.toNat + 4 := by
  simp only [BitVec.addInt, BitVec.toNat_add]
  rw [show (BitVec.ofInt 64 4).toNat = 4 by decide]
  exact Nat.mod_eq_of_lt h

theorem fetch_spec {code : List Ins} {pc : BitVec 64} {i : Ins} (h : fetch code pc = some i) :
    codeBase ≤ pc.toNat ∧ pc.toNat % 4 = 0 ∧ pc.toNat + 4 ≤ tohostAddr ∧
      code[(pc.toNat - codeBase) / 4]? = some i := by
  unfold fetch at h
  split at h
  · rename_i hc; exact ⟨hc.1, hc.2.1, hc.2.2, h⟩
  · cases h

theorem fetch_bytes {code : List Ins} {m : Mem} {pc : BitVec 64} {i : Ins}
    (hcode : CodeAt m code) (h : fetch code pc = some i) :
    ∀ j < 4, m[pc.toNat + j]? = some (byte i.encode j) := by
  obtain ⟨h1, h2, _, h4⟩ := fetch_spec h
  intro j hj
  have := hcode _ i h4 j hj
  rwa [show codeBase + 4 * ((pc.toNat - codeBase) / 4) + j = pc.toNat + j by
    simp only [codeBase] at h1 ⊢; omega] at this

theorem lookupG_eraseG_ne {n k : Nat} (hne : n ≠ k) :
    ∀ L : GRegs, lookupG n (eraseG k L) = lookupG n L
  | [] => rfl
  | (m, v) :: L => by
    simp only [eraseG, lookupG]
    split
    · rename_i hm; subst hm
      rw [if_neg (Ne.symm hne)]; exact lookupG_eraseG_ne hne L
    · simp only [lookupG]
      split
      · rfl
      · exact lookupG_eraseG_ne hne L

theorem mem_eraseG_of {p : Nat × BitVec 64} {n : Nat} :
    ∀ {L : GRegs}, p ∈ L → p.1 ≠ n → p ∈ eraseG n L
  | (m, w) :: L, h, hne => by
    simp only [eraseG]
    rcases List.mem_cons.mp h with rfl | h
    · rw [if_neg hne]; exact List.mem_cons_self ..
    · split
      · exact mem_eraseG_of h hne
      · exact List.mem_cons_of_mem _ (mem_eraseG_of h hne)

theorem mem_eraseAll_of {p : Nat × BitVec 64} :
    ∀ {S : List Nat} {L : GRegs}, p ∈ L → p.1 ∉ S → p ∈ eraseAll S L
  | [], _, h, _ => h
  | n :: S, L, h, hS => by
    simp only [List.mem_cons, not_or] at hS
    exact mem_eraseAll_of (S := S) (L := eraseG n L) (mem_eraseG_of h hS.1) hS.2

theorem Corr.sub {c : Config} {pc : BitVec 64} {L1 L2 : GRegs} {m : Mem} {o : Array String}
    (hc : Corr c ⟨pc, L1, m, o⟩) (hsub : ∀ p ∈ L2, p ∈ L1) : Corr c ⟨pc, L2, m, o⟩ := by
  refine ⟨hc.good, hc.tick, hc.pc, ?_, ?_, hc.mem, hc.out, hc.pw⟩
  · have hL := hc.regs
    rw [gholds_iff] at hL ⊢
    exact fun p hp => hL p (hsub p hp)
  · intro k hk
    obtain ⟨v, hv⟩ := keysG_mem hk
    exact hc.keys k (mem_keysG (hsub _ hv))

theorem ld_memFacts (m : Mem) (L : GRegs) (rd rs1 : Nat) (pc : BitVec 64)
    (hb : 0x80000000 ≤ (srcVal rs1 L).toNat ∧ (srcVal rs1 L).toNat + 8 ≤ 0x100000000 ∧
      ((srcVal rs1 L).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (srcVal rs1 L).toNat)) :
    MemFacts m L (rd8 m (srcVal rs1 L).toNat) ((Ins.ld rd rs1).toM pc) := by
  have he : eaddrM ((Ins.ld rd rs1).toM pc) L = srcVal rs1 L := by
    show srcVal rs1 L + sign_extend (m := 64) (0#12) = _
    rw [sext12_zero, BitVec.add_zero]
  show (0x80000000 ≤ (eaddrM _ L).toNat ∧ _ ∧ _) ∧ LPins8 m (eaddrM _ L).toNat _
  rw [he]
  exact ⟨hb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sim_libcall (off : BitVec 21) {A A' : AM} {c : Config} (hc : Corr c A)
    (hb : ∀ j < 4, A.mem[A.pc.toNat + j]? = some (byte (Ins.jal 1 off).encode j))
    (hlo : 0x80000000 ≤ A.pc.toNat) (hhi : A.pc.toNat + 4 ≤ tohostAddr)
    (hal : A.pc.toNat % 4 = 0)
    (htgt : (A.pc + sign_extend (m := 64) (evenJ off)).toNat % 4 = 0)
    (hlib : LibLoaded A.mem)
    (h : libCall (A.pc + sign_extend (m := 64) (evenJ off)).toNat A = some (.run A')) :
    StepsCorr c A' := by
  obtain ⟨c1, hs1, hlt1, hc1⟩ := (sim_jal_link off hc hb hlo hhi hal htgt).toSC
  have hret : (BitVec.addInt A.pc 4).toNat % 4 = 0 := by
    rw [addInt4_toNat _ (by simp only [tohostAddr] at hhi; omega)]; omega
  have hr : lookupG 1 ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) = some (BitVec.addInt A.pc 4) := by
    simp [lookupG]
  have hlk : ∀ n, n ≠ 1 → lookupG n ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) = lookupG n A.regs := by
    intro n hn
    simp only [lookupG, if_neg (Ne.symm hn)]
    exact lookupG_eraseG_ne hn A.regs
  have hkey : ∀ n, n ≠ 1 → n ∈ keysG A.regs → n ∈ keysG ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) :=
    fun n hn hk => List.mem_cons_of_mem _ (mem_keysG_eraseG hn _ hk)
  have hsub : ∀ res : BitVec 64, ∀ p ∈ (10, res) :: eraseAll clobbered A.regs,
      p ∈ (10, res) :: eraseAll clobbered ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) := by
    intro res p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_cons_self ..
    · obtain ⟨hpL, hpS⟩ := mem_eraseAll hp
      refine List.mem_cons_of_mem _ (mem_eraseAll_of (List.mem_cons_of_mem _ (mem_eraseG_of hpL ?_)) hpS)
      intro h1; exact hpS (by rw [h1]; simp [clobbered])
  have hlib1 : LibLoaded (AM.mk (A.pc + sign_extend (m := 64) (evenJ off))
      ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) A.mem A.out).mem := hlib
  unfold libCall at h
  split at h
  · rename_i x y hx hy
    split at h
    · rename_i hk
      have h12 := hkey 12 (by decide) hk.1
      have h13 := hkey 13 (by decide) hk.2
      have hx' := (hlk 10 (by decide)).trans hx
      have hy' := (hlk 11 (by decide)).trans hy
      have fin : ∀ res c', Steps c1 c' →
          Corr c' ⟨BitVec.addInt A.pc 4, (10, res) :: eraseAll clobbered
            ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs), A.mem, A.out⟩ →
          StepsCorr c ⟨BitVec.addInt A.pc 4, (10, res) :: eraseAll clobbered A.regs, A.mem, A.out⟩ :=
        fun res c' hs hc' => ⟨c', hs1.trans hs, Nat.lt_of_lt_of_le hlt1 hs.steps_le,
          hc'.sub (hsub res)⟩
      split at h
      · rename_i hm; cases h
        obtain ⟨c', hs, hc'⟩ := sim_mul hc1 (BitVec.eq_of_toNat_eq (by rw [hm]; rfl)) hr hret hx' hy'
          h12 h13 hlib1
        exact fin _ c' hs hc'
      · split at h
        · rename_i hd; cases h
          obtain ⟨c', hs, hc'⟩ := sim_div hc1 (BitVec.eq_of_toNat_eq (by rw [hd.1]; rfl)) hr hret
            hx' hy' hd.2 h12 h13 hlib1
          exact fin _ c' hs hc'
        · split at h
          · rename_i hd; cases h
            obtain ⟨c', hs, hc'⟩ := sim_mod hc1 (BitVec.eq_of_toNat_eq (by rw [hd.1]; rfl)) hr
              hret hx' hy' hd.2 h12 h13 hlib1
            exact fin _ c' hs hc'
          · cases h
    · cases h
  · cases h

theorem step_sim {code : List Ins} {A A' : AM} {c : Config} (hc : Corr c A)
    (hcode : CodeAt A.mem code) (hlib : LibLoaded A.mem)
    (h : astep code A = some (.run A')) :
    StepsCorr c A' := by
  unfold astep at h
  split at h
  · rename_i i hf
    obtain ⟨hcb, hal, hhi, _⟩ := fetch_spec hf
    have hb := fetch_bytes hcode hf
    have hlo : 0x80000000 ≤ A.pc.toNat := by simp only [codeBase] at hcb; omega
    cases i with
    | addi rd rs1 imm =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact Step1Corr.toSC <| sim_M (.addi rd rs1 imm) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) from hk).1)
      · cases h
    | ori rd rs1 imm =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact Step1Corr.toSC <| sim_M (.ori rd rs1 imm) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) from hk).1)
      · cases h
    | slli rd rs1 sh =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact Step1Corr.toSC <| sim_M (.slli rd rs1 sh) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) from hk).1)
      · cases h
    | add rd rs1 rs2 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact Step1Corr.toSC <| sim_M (.add rd rs1 rs2) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) ∧ SrcOK rs2 (keysG A.regs) from hk).1)
      · cases h
    | sub rd rs1 rs2 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact Step1Corr.toSC <| sim_M (.sub rd rs1 rs2) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) ∧ SrcOK rs2 (keysG A.regs) from hk).1)
      · cases h
    | slt rd rs1 rs2 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact Step1Corr.toSC <| sim_M (.slt rd rs1 rs2) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) ∧ SrcOK rs2 (keysG A.regs) from hk).1)
      · cases h
    | and rd rs1 rs2 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact Step1Corr.toSC <| sim_M (.and rd rs1 rs2) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) ∧ SrcOK rs2 (keysG A.regs) from hk).1)
      · cases h
    | ld rd rs1 =>
      simp only [exec] at h; split at h
      · rename_i hk; split at h
        · rename_i hbd; cases h
          exact Step1Corr.toSC <| sim_M (.ld rd rs1) trivial hc hb hlo hhi hal hk _ (ld_memFacts _ _ _ _ _ hbd)
            (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) from hk).1)
        · cases h
      · cases h
    | sd rs2 rs1 =>
      simp only [exec] at h; split at h
      · rename_i hk; split at h
        · rename_i hea
          unfold htifOut at h
          split at h; · cases h
          split at h; · cases h
          split at h
          · rename_i hv; cases h
            exact Step1Corr.toSC <| sim_putc hc rs2 rs1 hb hlo hhi hal hk.1 hk.2 hea hv
          · cases h
        · split at h
          · rename_i hbd; cases h
            have he : eaddrM ((Ins.sd rs2 rs1).toM A.pc) A.regs = srcVal rs1 A.regs := by
              show srcVal rs1 A.regs + sign_extend (m := 64) (0#12) = _
              rw [sext12_zero, BitVec.add_zero]
            have hmf : MemFacts A.mem A.regs [] ((Ins.sd rs2 rs1).toM A.pc) := by
              show 0x80000000 ≤ (eaddrM _ A.regs).toNat ∧ _
              rw [he]; exact hbd
            obtain ⟨c', hs, hlt, hc'⟩ := sim_M (.sd rs2 rs1) trivial hc hb hlo hhi hal
              ⟨hk.1, hk.2⟩ [] hmf (Or.inl rfl)
            refine ⟨c', hs, by omega, ?_⟩
            have hm : stepMemM A.mem ((Ins.sd rs2 rs1).toM A.pc) A.regs
                = applyW A.mem ((srcVal rs1 A.regs).toNat, 8, srcVal rs2 A.regs) := by
              show applyW A.mem ((eaddrM _ A.regs).toNat, 8, srcVal rs2 A.regs) = _
              rw [he]
            rw [hm] at hc'; exact hc'
          · cases h
      · cases h
    | br op rs1 rs2 off =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        obtain ⟨c', hs, hlt, hc'⟩ := sim_T (.br op rs1 rs2 off) trivial
          (guardB op.bop (srcVal rs1 A.regs) (srcVal rs2 A.regs)) hc hb hlo hhi hal hk rfl
        refine ⟨c', hs, by omega, ?_⟩
        revert hc'
        cases guardB op.bop (srcVal rs1 A.regs) (srcVal rs2 A.regs) <;> exact id
      · cases h
    | jal rd off =>
      simp only [exec] at h
      split at h
      · rename_i htgt
        split at h
        · rename_i hrd; subst hrd; cases h
          exact Step1Corr.toSC <| sim_T (.jal 0 off) rfl false hc hb hlo hhi hal htgt trivial
        · split at h
          · rename_i hrd0 hrd; subst hrd
            split at h
            · rename_i hlibt
              exact sim_libcall off hc hb hlo hhi hal htgt hlib h
            · cases h
              exact Step1Corr.toSC <| sim_jal_link off hc hb hlo hhi hal htgt
          · cases h
      · cases h
    | jalr rs1 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact Step1Corr.toSC <| sim_T (.jalr rs1) trivial false hc hb hlo hhi hal hk.1 hk.2
      · cases h
  · cases h

theorem step_sim1 {code : List Ins} {A A' : AM} {c : Config} (hc : Corr c A)
    (hcode : CodeAt A.mem code)
    (hnl : ∀ off, fetch code A.pc = some (.jal 1 off) →
      ¬ ((A.pc + sign_extend (m := 64) (evenJ off)).toNat = mulPC ∨
        (A.pc + sign_extend (m := 64) (evenJ off)).toNat = divPC ∨
        (A.pc + sign_extend (m := 64) (evenJ off)).toNat = modPC))
    (h : astep code A = some (.run A')) :
    Step1Corr c A' := by
  unfold astep at h
  split at h
  · rename_i i hf
    obtain ⟨hcb, hal, hhi, _⟩ := fetch_spec hf
    have hb := fetch_bytes hcode hf
    have hlo : 0x80000000 ≤ A.pc.toNat := by simp only [codeBase] at hcb; omega
    cases i with
    | addi rd rs1 imm =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact sim_M (.addi rd rs1 imm) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) from hk).1)
      · cases h
    | ori rd rs1 imm =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact sim_M (.ori rd rs1 imm) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) from hk).1)
      · cases h
    | slli rd rs1 sh =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact sim_M (.slli rd rs1 sh) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) from hk).1)
      · cases h
    | add rd rs1 rs2 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact sim_M (.add rd rs1 rs2) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) ∧ SrcOK rs2 (keysG A.regs) from hk).1)
      · cases h
    | sub rd rs1 rs2 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact sim_M (.sub rd rs1 rs2) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) ∧ SrcOK rs2 (keysG A.regs) from hk).1)
      · cases h
    | slt rd rs1 rs2 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact sim_M (.slt rd rs1 rs2) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) ∧ SrcOK rs2 (keysG A.regs) from hk).1)
      · cases h
    | and rd rs1 rs2 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact sim_M (.and rd rs1 rs2) trivial hc hb hlo hhi hal hk [] trivial
          (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) ∧ SrcOK rs2 (keysG A.regs) from hk).1)
      · cases h
    | ld rd rs1 =>
      simp only [exec] at h; split at h
      · rename_i hk; split at h
        · rename_i hbd; cases h
          exact sim_M (.ld rd rs1) trivial hc hb hlo hhi hal hk _ (ld_memFacts _ _ _ _ _ hbd)
            (Or.inr (show (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 (keysG A.regs) from hk).1)
        · cases h
      · cases h
    | sd rs2 rs1 =>
      simp only [exec] at h; split at h
      · rename_i hk; split at h
        · rename_i hea
          unfold htifOut at h
          split at h; · cases h
          split at h; · cases h
          split at h
          · rename_i hv; cases h
            exact sim_putc hc rs2 rs1 hb hlo hhi hal hk.1 hk.2 hea hv
          · cases h
        · split at h
          · rename_i hbd; cases h
            have he : eaddrM ((Ins.sd rs2 rs1).toM A.pc) A.regs = srcVal rs1 A.regs := by
              show srcVal rs1 A.regs + sign_extend (m := 64) (0#12) = _
              rw [sext12_zero, BitVec.add_zero]
            have hmf : MemFacts A.mem A.regs [] ((Ins.sd rs2 rs1).toM A.pc) := by
              show 0x80000000 ≤ (eaddrM _ A.regs).toNat ∧ _
              rw [he]; exact hbd
            obtain ⟨c', hs, hlt, hc'⟩ := sim_M (.sd rs2 rs1) trivial hc hb hlo hhi hal
              ⟨hk.1, hk.2⟩ [] hmf (Or.inl rfl)
            refine ⟨c', hs, hlt, ?_⟩
            have hm : stepMemM A.mem ((Ins.sd rs2 rs1).toM A.pc) A.regs
                = applyW A.mem ((srcVal rs1 A.regs).toNat, 8, srcVal rs2 A.regs) := by
              show applyW A.mem ((eaddrM _ A.regs).toNat, 8, srcVal rs2 A.regs) = _
              rw [he]
            rw [hm] at hc'; exact hc'
          · cases h
      · cases h
    | br op rs1 rs2 off =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        obtain ⟨c', hs, hlt, hc'⟩ := sim_T (.br op rs1 rs2 off) trivial
          (guardB op.bop (srcVal rs1 A.regs) (srcVal rs2 A.regs)) hc hb hlo hhi hal hk rfl
        refine ⟨c', hs, hlt, ?_⟩
        revert hc'
        cases guardB op.bop (srcVal rs1 A.regs) (srcVal rs2 A.regs) <;> exact id
      · cases h
    | jal rd off =>
      simp only [exec] at h
      split at h
      · rename_i htgt
        split at h
        · rename_i hrd; subst hrd; cases h
          exact sim_T (.jal 0 off) rfl false hc hb hlo hhi hal htgt trivial
        · split at h
          · rename_i hrd0 hrd; subst hrd
            split at h
            · rename_i hlibt
              exact absurd hlibt (hnl off hf)
            · cases h
              exact sim_jal_link off hc hb hlo hhi hal htgt
          · cases h
      · cases h
    | jalr rs1 =>
      simp only [exec] at h; split at h
      · rename_i hk; cases h
        exact sim_T (.jalr rs1) trivial false hc hb hlo hhi hal hk.1 hk.2
      · cases h
  · cases h

theorem halt_sim {code : List Ins} {A : AM} {e : Nat} {c : Config} (hc : Corr c A)
    (hcode : CodeAt A.mem code) (h : astep code A = some (.halt e)) :
    ∃ σf, Halted c e σf ∧ output σf = String.join A.out.toList := by
  unfold astep at h
  split at h
  · rename_i i hf
    obtain ⟨hcb, hal, hhi, _⟩ := fetch_spec hf
    have hb := fetch_bytes hcode hf
    have hlo : 0x80000000 ≤ A.pc.toNat := by simp only [codeBase] at hcb; omega
    cases i with
    | sd rs2 rs1 =>
      simp only [exec] at h; split at h
      · rename_i hk; split at h
        · rename_i hea
          unfold htifOut at h
          split at h
          · rename_i hv; cases h
            exact sim_exit 0 (by decide) hc rs2 rs1 hb hlo hhi hal hk.1 hk.2 hea hv
          split at h
          · rename_i hv; cases h
            exact sim_exit 70 (by decide) hc rs2 rs1 hb hlo hhi hal hk.1 hk.2 hea hv
          split at h <;> cases h
        · split at h <;> cases h
      · cases h
    | jal rd off =>
      simp only [exec] at h
      split at h
      · split at h
        · cases h
        · split at h
          · split at h
            · unfold libCall at h
              repeat' split at h
              all_goals cases h
            · cases h
          · cases h
      · cases h
    | _ =>
      simp only [exec] at h
      repeat' split at h
      all_goals cases h
  · cases h

#print axioms astep_mem_low
#print axioms step_sim
#print axioms halt_sim
#print axioms CodeAt.of_low
#print axioms LibLoaded.of_low

end Vsa.Compiler

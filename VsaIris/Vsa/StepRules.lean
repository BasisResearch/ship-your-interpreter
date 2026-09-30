import VsaIris.Vsa.SymExec
import VsaIris.Interp.IRun
import VsaIris.Vsa.AllocRun
import VsaIris.Interp.EnvRun
import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SnpRunDef

/-!
# Step rules with the landed continuation shape

One rule per instruction class (ALU line, owned load, store, branch, jump, return), proved
once from `swpx_line`/`swpx_br`/`swpx_j`/`swpx_jr` for any code image. A step-table lemma
at a literal `pc` is the rule applied to the instruction of the image word, one Boolean
side-condition check and the decode fact of the word; its binders and continuation are the
rule's, so the kernel identifies the table statement with the rule instance by evaluation.
`d*` rules are for runs with a data view (`T ++ dataOf Dt DA`), `a*` rules for runs without.
-/

namespace VsaIris.SymExec

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1

/-- What a step rule needs of a run: its code image, `PC` tracked, `gp` read-only. -/
structure TblOK (T : List (Nat × BitVec 8)) (rs : List Nat) (ps : List TextPiece)
    (img : Nat → BitVec 8) (rT : List (Nat × Nat)) : Prop where
  code : CodeAt T img rT
  foot : ∀ {i : Nat} {code : List (BitVec 8)}, bytesHasB ps i code = true →
    ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ T
  pc : VsaIris.PC ∈ rs
  gp : gp ∉ rs

/-- A text containing the footprint of `ps` pins every piece of `ps`. -/
theorem codeAt_of_piece {T : List (Nat × BitVec 8)} {ps : List TextPiece} {img : Nat → BitVec 8}
    {rT : List (Nat × Nat)} (hT : ∀ m : Mem, TextLoaded T m → TextIn (piecesText ps) m)
    (hp : (⟨img, rT⟩ : TextPiece) ∈ ps) : CodeAt T img rT := by
  intro m hm a ha
  refine (hT m hm).pin (List.any_eq_true.2 ⟨_, hp, ?_⟩)
  simp only [Bool.and_eq_true, beq_self_eq_true, and_true]
  exact inRangesB_iff.2 ha

theorem swp_nilD {live : Nat → Prop} {T : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} : SWP live (T ++ dataOf ∅ []) rs S Q pc R Mt ↔ SWP live T rs S Q pc R Mt := by
  rw [show dataOf ∅ [] = [] from rfl, List.append_nil]

/-! ## Side conditions -/

def aluChk (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat) (a : MInstr) : Bool :=
  lineChk img rT rs a && !isLoadK a.kind && !isStoreK a.kind

def loadChk (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat) (a : MInstr) : Bool :=
  lineChk img rT rs a && isLoadK a.kind

/-- A load at a `gp`-relative (constant) address inside RAM. -/
def loadcChk (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat) (a : MInstr) : Bool :=
  loadChk img rT rs a && decide (a.rs1 = gp) &&
    decide (LdOK (gpV + sext12 a.imm).toNat (widthOfM a.kind))

def storeChk (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat) (a : MInstr) : Bool :=
  lineChk img rT rs a && isStoreK a.kind

/-- The store side condition as the tables state it (no alignment for a byte). -/
def stOKk : MKind → Nat → Prop
  | .sb, ea => StOKb ea
  | k, ea => StOK ea (widthOfM k)

/-- A branch condition as the tables state it. -/
def brCond : bop → BitVec 64 → BitVec 64 → Prop
  | .BEQ, a, b => a = b
  | .BNE, a, b => a ≠ b
  | .BLT, a, b => a.toInt < b.toInt
  | .BGE, a, b => b.toInt ≤ a.toInt
  | .BLTU, a, b => a.toNat < b.toNat
  | .BGEU, a, b => b.toNat ≤ a.toNat

theorem guardB_iff (op : bop) (a b : BitVec 64) : guardB op a b = true ↔ brCond op a b := by
  cases op
  · exact guard_beq a b
  · exact guard_bne a b
  · exact guard_blt a b
  · exact guard_bge a b
  · exact guard_bltu a b
  · exact guard_bgeu a b

theorem memFacts_alu {a : MInstr} (h1 : isLoadK a.kind = false) (h2 : isStoreK a.kind = false)
    (m : Mem) (L : GRegs) (l0 : List (BitVec 8)) : MemFacts m L l0 a := by
  unfold MemFacts
  revert h1 h2
  cases a.kind <;> intro h1 h2 <;> first | trivial | cases h1 | cases h2

theorem memFacts_storeK {a : MInstr} (h : isStoreK a.kind = true) {m : Mem} {L : GRegs}
    {l0 : List (BitVec 8)} (hea : stOKk a.kind (eaddrM a L).toNat) : MemFacts m L l0 a := by
  unfold MemFacts
  revert h hea
  cases a.kind <;> intro h hea <;> first | exact hea | cases h

section rules
variable {T : List (Nat × BitVec 8)} {rs : List Nat} {ps : List TextPiece}
  {img : Nat → BitVec 8} {rT : List (Nat × Nat)}

/-! ## Runs with a data view -/

theorem d_alu (C : TblOK T rs ps img rT) (a : MInstr) (hchk : aluChk img rT rs a = true)
    (hdec : DecM a) {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hk : SWP live (T ++ dataOf Dt DA) rs S Q (BitVec.addInt a.pc 4)
      (upd R a.rd (wvalM a (pinsOf (lineKs a) R) [])) Mt) :
    SWP live (T ++ dataOf Dt DA) rs S Q a.pc R Mt := by
  simp only [aluChk, Bool.and_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨hl, hnl⟩, hns⟩ := hchk
  have ok := LineOK.of_chk hl
  refine swpx_line img rT C.code a (lineKs a) [] [] [] ok.wf ok.keys ok.wr ?_ hlive ok.pins hdec
    (fun m _ _ _ => memFacts_alu hnl hns _ _ _) C.pc ok.regs ok.nogp C.gp
    (fun _ h => nomatch h) (fun _ h => nomatch h) ?_ ?_
  · intro b _; rw [hns]; trivial
  · intro x _ _ hnk
    rw [lineR_nonstore hns]
    exact upd_other _ _ fun e => hnk (e ▸ ok.wr a.rd (by rw [wrChain_nonstore hns]; simp))
  · rw [lineR_nonstore hns, hns]; exact hk

theorem d_load (C : TblOK T rs ps img rT) (a : MInstr) (hchk : loadChk img rT rs a = true)
    (hdec : DecM a) {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hea : LdOK (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind))
    (hLDS : ∀ b ∈ accAddrs (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind), S b)
    (hk : SWP live (T ++ dataOf Dt DA) rs S Q (BitVec.addInt a.pc 4)
      (upd R a.rd (ldv a.kind Mt (eaddrM a (pinsOf (lineKs a) R)).toNat)) Mt) :
    SWP live (T ++ dataOf Dt DA) rs S Q a.pc R Mt := by
  simp only [loadChk, Bool.and_eq_true] at hchk
  obtain ⟨hl, hld⟩ := hchk
  have hns := not_store_of_load hld
  have ok := LineOK.of_chk hl
  refine swpx_line img rT C.code a (lineKs a)
    [bytesAt (imgM Mt) (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind)]
    (accAddrs (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind)) []
    ok.wf ok.keys ok.wr ?_ hlive ok.pins hdec
    (fun m _ _ hLD => memFacts_load hld hea hLD) C.pc ok.regs ok.nogp C.gp
    hLDS (fun _ h => nomatch h) ?_ ?_
  · intro b _; rw [hns]; trivial
  · intro x _ _ hnk
    rw [lineR_nonstore hns]
    exact upd_other _ _ fun e => hnk (e ▸ ok.wr a.rd (by rw [wrChain_nonstore hns]; simp))
  · rw [lineR_nonstore hns, hns, wvalM_load hld]; exact hk

theorem d_store (C : TblOK T rs ps img rT) (a : MInstr) (hchk : storeChk img rT rs a = true)
    (hdec : DecM a) {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hea : stOKk a.kind (eaddrM a (pinsOf (lineKs a) R)).toNat)
    (hS : ∀ b ∈ accAddrs (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind), S b)
    (hk : SWP live (T ++ dataOf Dt DA) rs S Q (BitVec.addInt a.pc 4) R
      (writeLog Mt [wentryM a (pinsOf (lineKs a) R)])) :
    SWP live (T ++ dataOf Dt DA) rs S Q a.pc R Mt := by
  simp only [storeChk, Bool.and_eq_true] at hchk
  obtain ⟨hl, hst⟩ := hchk
  have ok := LineOK.of_chk hl
  refine swpx_line img rT C.code a (lineKs a) []
    [] (accAddrs (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind))
    ok.wf ok.keys ok.wr ?_ hlive ok.pins hdec
    (fun m _ _ _ => memFacts_storeK hst hea) C.pc ok.regs ok.nogp C.gp
    (fun _ h => nomatch h) hS ?_ ?_
  · intro b hb; rw [hst]; exact outL_single _ hb
  · intro x _ _ _; unfold lineR; rw [hst]; rfl
  · unfold lineR; rw [hst]; exact hk

theorem d_br (C : TblOK T rs ps img rT) (pc : BitVec 64) (w : BitVec 32) (op : bop) (r1 r2 : Nat)
    (i13 : BitVec 13)
    (hchk : brChk img rT rs (mkT pc w (.br op true) r1 r2 i13 0)
      (mkT pc w (.br op false) r1 r2 i13 0) (nzd [r1, r2]) = true)
    (hdec : DecT (mkT pc w (.br op true) r1 r2 i13 0))
    {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hT : brCond op (rdR R r1) (rdR R r2) → SWP live (T ++ dataOf Dt DA) rs S Q
      (tgtPC0 (mkT pc w (.br op true) r1 r2 i13 0)) R Mt)
    (hF : ¬ brCond op (rdR R r1) (rdR R r2) → SWP live (T ++ dataOf Dt DA) rs S Q
      (tgtPC0 (mkT pc w (.br op false) r1 r2 i13 0)) R Mt) :
    SWP live (T ++ dataOf Dt DA) rs S Q pc R Mt := by
  have ok := BrOK.of_chk hchk
  have h1 : r1 = 0 ∨ r1 ∈ nzd [r1, r2] := mem_nzd (by simp)
  have h2 : r2 = 0 ∨ r2 ∈ nzd [r1, r2] := mem_nzd (by simp)
  have hg : ∀ b, (guardB op (rdR R r1) (rdR R r2) = b) →
      guardB op (srcVal r1 (pinsOf (nzd [r1, r2]) R)) (srcVal r2 (pinsOf (nzd [r1, r2]) R)) = b :=
    fun b h => by rw [srcVal_pins h1, srcVal_pins h2]; exact h
  by_cases hc : brCond op (rdR R r1) (rdR R r2)
  · exact swpx_br img rT C.code (mkT pc w (.br op true) r1 r2 i13 0) op true rfl
      (nzd [r1, r2]) ok.wft ok.keys hlive ok.pins hdec (hg _ ((guardB_iff _ _ _).2 hc)) C.pc
      ok.regs C.gp (hT hc)
  · exact swpx_br img rT C.code (mkT pc w (.br op false) r1 r2 i13 0) op false rfl
      (nzd [r1, r2]) ok.wff ok.keys hlive ok.pins (fun σ => hdec σ)
      (hg _ ((guard_false (guardB_iff _ _ _)).2 hc)) C.pc ok.regs C.gp (hF hc)

theorem d_j (C : TblOK T rs ps img rT) (pc : BitVec 64) (w : BitVec 32) (i21 : BitVec 21)
    (hchk : jChk img rT (mkT pc w .j 0 0 0 i21) = true) (hdec : DecT (mkT pc w .j 0 0 0 i21))
    {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hk : SWP live (T ++ dataOf Dt DA) rs S Q (tgtPC0 (mkT pc w .j 0 0 0 i21)) R Mt) :
    SWP live (T ++ dataOf Dt DA) rs S Q pc R Mt := by
  simp only [jChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  exact swpx_j img rT C.code (mkT pc w .j 0 0 0 i21) rfl hchk.1 hlive hchk.2 hdec C.pc C.gp hk

theorem d_jr (C : TblOK T rs ps img rT) (pc : BitVec 64) (w : BitVec 32) (r1 : Nat)
    (hchk : jrChk img rT rs (mkT pc w .jr r1 0 0 0) (nzd [r1]) = true)
    (hdec : DecT (mkT pc w .jr r1 0 0 0))
    {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hal : (rdR R r1).toNat % 4 = 0)
    (hk : SWP live (T ++ dataOf Dt DA) rs S Q (rdR R r1) R Mt) :
    SWP live (T ++ dataOf Dt DA) rs S Q pc R Mt := by
  simp only [jrChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hwf, hkeys⟩, hpins⟩, hregs⟩ := hchk
  have hsv : srcVal r1 (pinsOf (nzd [r1]) R) = rdR R r1 := srcVal_pins (mem_nzd (by simp))
  exact swpx_jr img rT C.code (mkT pc w .jr r1 0 0 0) rfl rfl (nzd [r1]) hwf hkeys hlive hpins
    hdec C.pc hregs C.gp (by show (srcVal r1 _).toNat % 4 = 0; rw [hsv]; exact hal)
    (by show SWP _ _ _ _ _ (srcVal r1 _) _ _; rw [hsv]; exact hk)

/-- The bytes of an instruction word, as a call site lists them. -/
def wbytes (w : BitVec 32) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- Decidable side conditions of `jal ra, imm` with word `w` at `pc` and target `tgt`. -/
def jalChk (pc : Nat) (w : BitVec 32) (imm : BitVec 21) (tgt : BitVec 64) : Bool :=
  decide (pc < 2 ^ 64) && decide (0x80000000 ≤ pc) && decide (pc + 4 ≤ tohostAddr) &&
  decide (pc % 4 = 0) &&
  decide (Sail.BitVec.extractLsb ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
    (w.extractLsb' 8 8)).append (w.extractLsb' 0 8)) 1 0 = (0b11#2 : BitVec 2)) &&
  decide ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
    (w.extractLsb' 8 8)).append (w.extractLsb' 0 8) = w) &&
  decide (BitVec.ofNat 64 pc + sign_extend (m := 64) imm = tgt) && decide (tgt.toNat % 4 = 0) &&
  decide (BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4))

/-- `jal ra` at `pc`: its `JalExec` fact, for any word that decodes to it. -/
theorem jalExec_word (pc : Nat) (w : BitVec 32) (imm : BitVec 21) (tgt : BitVec 64)
    (hchk : jalChk pc w imm tgt = true)
    (hdec : ∀ σ, decodeN w σ = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) σ)
    (live : Nat → Prop) (hlive : ∀ p ∈ codeFoot pc (wbytes w), live p.1) :
    JalExec (vsaModel live) pc (wbytes w) tgt := by
  simp only [jalChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlt, hlo⟩, hhi⟩, hal⟩, hrvc⟩, hword⟩, htgt⟩, htal⟩, hlink⟩ := hchk
  have hpn : (BitVec.ofNat 64 pc).toNat = pc := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (pc + 0, .discard, w.extractLsb' 0 8) (by simp [codeFoot, wbytes])
  have hb1 := hb (pc + 1, .discard, w.extractLsb' 8 8) (by simp [codeFoot, wbytes])
  have hb2 := hb (pc + 2, .discard, w.extractLsb' 16 8) (by simp [codeFoot, wbytes])
  have hb3 := hb (pc + 3, .discard, w.extractLsb' 24 8) (by simp [codeFoot, wbytes])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (BitVec.ofNat 64 pc) vm w imm
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (BitVec.ofNat 64 pc) 4)
      _ _ _ _ hG hpc hmi (by rw [hpn]; exact hb0) (by rw [hpn]; exact hb1)
      (by rw [hpn]; exact hb2) (by rw [hpn]; exact hb3)
      (by rw [hpn]; exact hlo) (by rw [hpn]; exact hhi) (by rw [hpn]; exact hal) hrvc hword
      (Vsa.Sim.decodeW (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg) (hdec _))
      (by rw [htgt]; exact htal) (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (BitVec.ofNat 64 pc) 4)) hi
  have h := jalStep_of_obs (calleeEntry := tgt) hs hi' hG' hmem hobs htgt
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [hlink] at h

/-- A call `jal ra, tgt` of a run with a data view. -/
theorem d_jal (C : TblOK T rs ps img rT) (pc : Nat) (w : BitVec 32) (imm : BitVec 21)
    (tgt : BitVec 64)
    (hchk : (jalChk pc w imm tgt && bytesHasB ps pc (wbytes w) && decide (VsaIris.ra ∈ rs)) = true)
    (hdec : ∀ σ, decodeN w σ = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) σ)
    {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hk : SWP live (T ++ dataOf Dt DA) rs S Q tgt
      (upd R VsaIris.ra (BitVec.ofNat 64 (pc + 4))) Mt) :
    SWP live (T ++ dataOf Dt DA) rs S Q (BitVec.ofNat 64 pc) R Mt := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨hj, hb⟩, hra⟩ := hchk
  exact swp_jal pc (wbytes w) tgt
    (jalExec_word pc w imm tgt hj hdec live fun p hp => hlive _ (C.foot hb p hp))
    (fun p hp => List.mem_append_left _ (C.foot hb p hp)) C.pc hra rfl hk

/-! ## Runs without a data view -/

theorem a_alu (C : TblOK T rs ps img rT) (a : MInstr) (hchk : aluChk img rT rs a = true)
    (hdec : DecM a) {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hk : SWP live T rs S Q (BitVec.addInt a.pc 4)
      (upd R a.rd (wvalM a (pinsOf (lineKs a) R) [])) Mt) :
    SWP live T rs S Q a.pc R Mt :=
  swp_nilD.1 <| d_alu C a hchk hdec hlive (swp_nilD.2 hk)

theorem a_load (C : TblOK T rs ps img rT) (a : MInstr) (hchk : loadChk img rT rs a = true)
    (hdec : DecM a) {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hea : LdOK (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind))
    (hLDS : ∀ b ∈ accAddrs (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind), S b)
    (hk : SWP live T rs S Q (BitVec.addInt a.pc 4)
      (upd R a.rd (ldv a.kind Mt (eaddrM a (pinsOf (lineKs a) R)).toNat)) Mt) :
    SWP live T rs S Q a.pc R Mt :=
  swp_nilD.1 <| d_load C a hchk hdec hlive hea hLDS (swp_nilD.2 hk)

/-- A load at a `gp`-relative address: the range condition is part of the check. -/
theorem a_loadc (C : TblOK T rs ps img rT) (a : MInstr) (hchk : loadcChk img rT rs a = true)
    (hdec : DecM a) {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hLDS : ∀ b ∈ accAddrs (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind), S b)
    (hk : SWP live T rs S Q (BitVec.addInt a.pc 4)
      (upd R a.rd (ldv a.kind Mt (eaddrM a (pinsOf (lineKs a) R)).toNat)) Mt) :
    SWP live T rs S Q a.pc R Mt := by
  simp only [loadcChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨hl, hr⟩, hea⟩ := hchk
  refine a_load C a hl hdec hlive ?_ hLDS hk
  have h1 : a.rs1 = 0 ∨ a.rs1 ∈ lineKs a := rs1_mem a
  unfold eaddrM
  rw [srcVal_pins h1, hr]
  exact hea

theorem a_store (C : TblOK T rs ps img rT) (a : MInstr) (hchk : storeChk img rT rs a = true)
    (hdec : DecM a) {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hea : stOKk a.kind (eaddrM a (pinsOf (lineKs a) R)).toNat)
    (hS : ∀ b ∈ accAddrs (eaddrM a (pinsOf (lineKs a) R)).toNat (widthOfM a.kind), S b)
    (hk : SWP live T rs S Q (BitVec.addInt a.pc 4) R
      (writeLog Mt [wentryM a (pinsOf (lineKs a) R)])) :
    SWP live T rs S Q a.pc R Mt :=
  swp_nilD.1 <| d_store C a hchk hdec hlive hea hS (swp_nilD.2 hk)

theorem a_br (C : TblOK T rs ps img rT) (pc : BitVec 64) (w : BitVec 32) (op : bop) (r1 r2 : Nat)
    (i13 : BitVec 13)
    (hchk : brChk img rT rs (mkT pc w (.br op true) r1 r2 i13 0)
      (mkT pc w (.br op false) r1 r2 i13 0) (nzd [r1, r2]) = true)
    (hdec : DecT (mkT pc w (.br op true) r1 r2 i13 0))
    {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hT : brCond op (rdR R r1) (rdR R r2) → SWP live T rs S Q
      (tgtPC0 (mkT pc w (.br op true) r1 r2 i13 0)) R Mt)
    (hF : ¬ brCond op (rdR R r1) (rdR R r2) → SWP live T rs S Q
      (tgtPC0 (mkT pc w (.br op false) r1 r2 i13 0)) R Mt) :
    SWP live T rs S Q pc R Mt :=
  swp_nilD.1 <| d_br C pc w op r1 r2 i13 hchk hdec hlive (fun h => swp_nilD.2 (hT h))
    (fun h => swp_nilD.2 (hF h))

theorem a_j (C : TblOK T rs ps img rT) (pc : BitVec 64) (w : BitVec 32) (i21 : BitVec 21)
    (hchk : jChk img rT (mkT pc w .j 0 0 0 i21) = true) (hdec : DecT (mkT pc w .j 0 0 0 i21))
    {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hk : SWP live T rs S Q (tgtPC0 (mkT pc w .j 0 0 0 i21)) R Mt) :
    SWP live T rs S Q pc R Mt :=
  swp_nilD.1 <| d_j C pc w i21 hchk hdec hlive (swp_nilD.2 hk)

theorem a_jr (C : TblOK T rs ps img rT) (pc : BitVec 64) (w : BitVec 32) (r1 : Nat)
    (hchk : jrChk img rT rs (mkT pc w .jr r1 0 0 0) (nzd [r1]) = true)
    (hdec : DecT (mkT pc w .jr r1 0 0 0))
    {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hal : (rdR R r1).toNat % 4 = 0)
    (hk : SWP live T rs S Q (rdR R r1) R Mt) :
    SWP live T rs S Q pc R Mt :=
  swp_nilD.1 <| d_jr C pc w r1 hchk hdec hlive hal (swp_nilD.2 hk)

theorem a_jal (C : TblOK T rs ps img rT) (pc : Nat) (w : BitVec 32) (imm : BitVec 21)
    (tgt : BitVec 64)
    (hchk : (jalChk pc w imm tgt && bytesHasB ps pc (wbytes w) && decide (VsaIris.ra ∈ rs)) = true)
    (hdec : ∀ σ, decodeN w σ = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) σ)
    {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ T, live p.1)
    (hk : SWP live T rs S Q tgt (upd R VsaIris.ra (BitVec.ofNat 64 (pc + 4))) Mt) :
    SWP live T rs S Q (BitVec.ofNat 64 pc) R Mt :=
  swp_nilD.1 <| d_jal C pc w imm tgt hchk hdec hlive (swp_nilD.2 hk)

end rules

/-- The decode obligation of a literal word, as the kernel checks it (by evaluation). -/
abbrev decRefl (w : BitVec 32) :
    ∀ σ : SequentialState RegisterType trivialChoiceSource, decodeN w σ = decodeN w σ :=
  fun _ => rfl

/-! ## The runs of this binary -/

open VsaIris.Newlib in
theorem interp_tblOK : TblOK interpText iRegs interpCodePieces textByte interpCodeRanges :=
  ⟨codeAt_of_piece (ps := interpCodePieces) (fun _ hm => TextIn.left hm) (by simp [interpCodePieces]),
    interp_code, by decide, by decide⟩

open VsaIris.Newlib in
theorem stdio_tblOK : TblOK stdioText iRegs stdioPieces textByte stdioCodeRanges :=
  ⟨codeAt_of_piece (ps := stdioPieces) (fun _ hm => TextIn.left hm) (by simp [stdioPieces]),
    stdio_code, by decide, by decide⟩

open VsaIris.Newlib in
theorem snp_tblOK : TblOK snpText nRegs snpPieces textByte snpCodeRanges :=
  ⟨codeAt_of_piece (ps := snpPieces) (fun _ hm => hm) (by simp [snpPieces]), snp_code, by decide,
    by decide⟩

open VsaIris.Newlib in
theorem alloc_tblOK : TblOK allocText aRegs allocPieces textByte allocCodeRanges :=
  ⟨codeAt_of_piece (ps := allocPieces) (fun _ hm => hm) (by simp [allocPieces]), alloc_code,
    by decide, by decide⟩

open VsaIris.Newlib in
theorem env_tblOK : TblOK envText eRegs envPieces textByte envCodeRanges :=
  ⟨codeAt_of_piece (ps := envPieces) (fun _ hm => hm) (by simp [envPieces]), env_code, by decide,
    by decide⟩

end VsaIris.SymExec

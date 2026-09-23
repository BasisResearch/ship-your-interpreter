import VsaIris.Vsa.StrlenSeg

/-!
# `strlen` as one bounded owned-footprint run

INTERP_DESIGN.md §9, package H3. The whole function — the alignment test, the
byte-peel loop, the word-at-a-time scan, the seven-way byte tail and the seven
return arms — is ONE `LocalRun` (`VsaIris/LocalRun.lean`), built segment by
segment with `strlenStep` (`StrlenSeg.lean`). Nothing here mentions Iris: the
Iris layer is a single `wp_localRunW` application in `StrlenSpec.lean`.

The zero-byte arithmetic is VSA's, reused by name: `StrlenMagic.detect_all_ones`
and its two consumers `detect_takenG`/`detect_nottakenG`.
-/

namespace VsaIris.Inst.Strlen

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Vsa.Sim Vsa.MemRepr

section Run

variable {live : Nat → Prop} {P r : BitVec 64} {len : Nat} {bv : Nat → BitVec 8}

/-- The RAM/HTIF geometry of the read region. Same fields as VSA's
`StrlenReadRegions` (`Vsa/Sim/StrlenReadState.lean`), restated here so that
this file does not depend on the runtime-ownership layer. -/
structure ReadRegions (P : BitVec 64) (len : Nat) : Prop where
  lo : 0x80000000 ≤ P.toNat
  hi : P.toNat + len + 8 ≤ 0x100000000
  nowrap : P.toNat + len + 8 < 2 ^ 64
  htif : P.toNat + len + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ P.toNat

/-- **The immutable side conditions of one `strlen` run.** The read region's
geometry (which already reserves the eight bytes the word loop over-reads),
the string's bytes, the caller's return alignment, and liveness of everything
the run reads. -/
structure Ctx (live : Nat → Prop) (P r : BitVec 64) (len : Nat) (bv : Nat → BitVec 8) :
    Prop where
  regions : ReadRegions P len
  str : StrBytes P.toNat len bv
  retAlign : r.toNat % 4 = 0
  codeLive : ∀ q ∈ strlenMR P.toNat len bv, live q.1

/-! ## Byte and word facts -/

/-- A byte of the region, as a total read. -/
theorem byteVal {m0 : Std.ExtHashMap Nat (BitVec 8)} (hread : Reads P.toNat len bv m0)
    (a : Nat) (ha : a < len + 8) : (m0[P.toNat + a]?).getD 0 = bv (P.toNat + a) := by
  rw [hread.bytes a ha]; rfl

/-- The byte at offset `a ≤ len` is NUL exactly at the terminator. -/
theorem byteBeq (ctx : Ctx live P r len bv) (a : Nat) (ha : a ≤ len) :
    (bv (P.toNat + a) == 0#8) = decide (a = len) := by
  by_cases he : a = len
  · subst he; rw [ctx.str.nul]; simp
  · have hne := ctx.str.nonzero a (by omega)
    simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
    exact hne

/-- The `lbu` of a tail test. -/
theorem lbuFact (ctx : Ctx live P r len bv) {m0 : Std.ExtHashMap Nat (BitVec 8)}
    (hread : Reads P.toNat len bv m0) (a : Nat) (ha : a < len + 8)
    (L : GRegs) (line : MInstr) (hkind : line.kind = .lbu)
    (haddr : (eaddrM line L).toNat = P.toNat + a) :
    MemFacts m0 L [bv (P.toNat + a)] line := by
  have hlo := ctx.regions.lo
  have hhi := ctx.regions.hi
  have hh := ctx.regions.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  unfold MemFacts
  rw [hkind]
  change (0x80000000 ≤ _ ∧ _ + 1 ≤ 0x100000000 ∧
    (_ + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ _)) ∧ _
  rw [haddr]
  refine ⟨⟨by omega, by omega, ?_⟩, ?_⟩
  · rcases hh with h | h
    · left; omega
    · right; omega
  · change (m0[P.toNat + a]?).getD 0 = _
    rw [byteVal hread a ha]
    rfl

/-- The address of a tail `lbu a5,-(8-k)(a4)` with `a4 = P + (t+8)`. -/
theorem tailAddr (ctx : Ctx live P r len bv) (t k : Nat) (hk : k ≤ 8)
    (htk : t + 8 ≤ len + 8) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k))) :
    (((P + BitVec.ofNat 64 (t + 8)) + sign_extend (m := 64) imm).toNat) = P.toNat + (t + k) := by
  have hstep : (P + BitVec.ofNat 64 (t + 8)) + sign_extend (m := 64) imm
      = P + BitVec.ofNat 64 (t + k) := by
    rw [himm, BitVec.add_assoc, BitVec.add_neg_eq_sub, ofNat_sub (t + 8) (8 - k) (by omega)]
    congr 2
    omega
  rw [hstep]
  exact ptrN P (t + k) (by have := ctx.regions.nowrap; omega)

/-- The value a return arm computes: `a3 - (8-k) = len` when the NUL sits at
offset `k` of the last word. -/
theorem armVal (t len k : Nat) (imm : BitVec 12) (hk : k ≤ 8) (hlen : t + k = len)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k))) :
    BitVec.ofNat 64 (t + 8) + sign_extend (m := 64) imm = BitVec.ofNat 64 len := by
  rw [himm, BitVec.add_neg_eq_sub, ofNat_sub (t + 8) (8 - k) (by omega)]
  congr 1
  omega

/-! ## The seven return arms

Each is `addi a0,a3,-(8-k); ret` with `a3 = t+8`: one segment, and the run is
over. -/

/-- **A return arm.** -/
theorem retArm (ctx : Ctx live P r len bv) {t k : Nat} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} (seg : List BBlock) (armPC : BitVec 64) (imm : BitVec 12) (n : Nat)
    (hfuel : evalBlocksFuel seg = n + 1)
    (hwf : ChainOK armPC strlenRegs seg)
    (hwr : ∀ j ∈ wrChain seg, j ∈ strlenRegs)
    (hlog : (segOut seg (strlenL rv) []).log = [])
    (hfacts : ∀ m0 : Std.ExtHashMap Nat (BitVec 8), Reads P.toNat len bv m0 →
      ChainFacts m0 m0 (strlenL rv) [] seg)
    (hpcOut : evalBlocksPC armPC (SegEvalState.init (strlenL rv) []) seg
      = Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1)
    (hfin10 : finReg seg (strlenL rv) [] 10 = rv 13 + sign_extend (m := 64) imm)
    (hfin1 : finReg seg (strlenL rv) [] 1 = rv 1)
    (hslack : ∀ a, slackSet P.toNat len a → mv a = bv a)
    (hpc : rv VsaIris.PC = armPC) (hra : rv 1 = r)
    (ha3 : rv 13 = BitVec.ofNat 64 (t + 8))
    (hk : k ≤ 8) (hlen : t + k = len)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k))) :
    SRun live P.toNat len bv r 1 rv mv := by
  refine strlenStep 0 seg [] armPC n hfuel hwf hwr hlog ctx.codeLive hslack hpc hfacts ?_
  intro rv' mv' hpc' hfin hslack'
  refine ⟨?_, ?_, ?_, hslack'⟩
  · rw [hpc', hpcOut, hra, ret_tgt r ctx.retAlign]
  · rw [hfin 1 (by simp [strlenRegs]), hfin1, hra]
  · rw [hfin 10 (by simp [strlenRegs]), hfin10, ha3, armVal t len k imm hk hlen himm]

/-! ## The byte tail `0x80006d2c … 0x80006d70`

The NUL lies at offset `k` of the word `[t, t+8)`. The tail tests offsets
`0 … 5` explicitly; offset `6` is tested by the `snez` block, which also
covers offset `7` without a test. -/

/-- At tail test `k` (`1 ≤ k ≤ 6`): `a3` holds `t+8` and `a4` holds `P+(t+8)`. -/
structure TailK (P r : BitVec 64) (len t k : Nat) (pc : BitVec 64)
    (rv : Nat → BitVec 64) : Prop where
  pcv : rv VsaIris.PC = pc
  ra : rv 1 = r
  a3 : rv 13 = BitVec.ofNat 64 (t + 8)
  a4 : rv 14 = P + BitVec.ofNat 64 (t + 8)
  lo : t + k ≤ len
  hi : len < t + 8

/-- At the tail entry `0x80006d2c`: `a0` still holds `P`. -/
structure TailAt (P r : BitVec 64) (len t : Nat) (rv : Nat → BitVec 64) : Prop where
  pcv : rv VsaIris.PC = 0x80006d2c#64
  ra : rv 1 = r
  a0 : rv 10 = P
  a4 : rv 14 = P + BitVec.ofNat 64 (t + 8)
  lo : t ≤ len
  hi : len < t + 8

/-- **One `lbu a5,-(8-k)(a4); beqz a5` tail test.** Both successors are
supplied; the reflected guard selects one. -/
theorem tailTest (ctx : Ctx live P r len bv) {t k m : Nat}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (segT segF : List BBlock) (nT nF : Nat) (pcK pcT pcF : BitVec 64)
    (hfuelT : evalBlocksFuel segT = nT + 1) (hfuelF : evalBlocksFuel segF = nF + 1)
    (hwfT : ChainOK pcK strlenRegs segT) (hwfF : ChainOK pcK strlenRegs segF)
    (hwrT : ∀ j ∈ wrChain segT, j ∈ strlenRegs) (hwrF : ∀ j ∈ wrChain segF, j ∈ strlenRegs)
    (hlogT : (segOut segT (strlenL rv) [[bv (P.toNat + (t + k))]]).log = [])
    (hlogF : (segOut segF (strlenL rv) [[bv (P.toNat + (t + k))]]).log = [])
    (hpcT : evalBlocksPC pcK (SegEvalState.init (strlenL rv) [[bv (P.toNat + (t + k))]]) segT
      = pcT)
    (hpcF : evalBlocksPC pcK (SegEvalState.init (strlenL rv) [[bv (P.toNat + (t + k))]]) segF
      = pcF)
    (hkeepT : ∀ j ∈ strlenRegs, j ≠ 15 →
      finReg segT (strlenL rv) [[bv (P.toNat + (t + k))]] j = rv j)
    (hkeepF : ∀ j ∈ strlenRegs, j ≠ 15 →
      finReg segF (strlenL rv) [[bv (P.toNat + (t + k))]] j = rv j)
    (hfactsT : t + k = len → ∀ m0 : Std.ExtHashMap Nat (BitVec 8), Reads P.toNat len bv m0 →
      ChainFacts m0 m0 (strlenL rv) [[bv (P.toNat + (t + k))]] segT)
    (hfactsF : t + k ≠ len → ∀ m0 : Std.ExtHashMap Nat (BitVec 8), Reads P.toNat len bv m0 →
      ChainFacts m0 m0 (strlenL rv) [[bv (P.toNat + (t + k))]] segF)
    (hslack : ∀ a, slackSet P.toNat len a → mv a = bv a)
    (hpc : rv VsaIris.PC = pcK)
    (hcontT : t + k = len → ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = pcT → (∀ j ∈ strlenRegs, j ≠ 15 → rv' j = rv j) →
      (∀ a, slackSet P.toNat len a → mv' a = bv a) → SRun live P.toNat len bv r m rv' mv')
    (hcontF : t + k ≠ len → ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = pcF → (∀ j ∈ strlenRegs, j ≠ 15 → rv' j = rv j) →
      (∀ a, slackSet P.toNat len a → mv' a = bv a) → SRun live P.toNat len bv r m rv' mv') :
    SRun live P.toNat len bv r (m + 1) rv mv := by
  by_cases he : t + k = len
  · refine strlenStep m segT _ pcK nT hfuelT hwfT hwrT hlogT ctx.codeLive hslack hpc
      (hfactsT he) ?_
    intro rv' mv' hpc' hfin hslack'
    exact hcontT he rv' mv' (by rw [hpc', hpcT])
      (fun j hj hj15 => by rw [hfin j hj, hkeepT j hj hj15]) hslack'
  · refine strlenStep m segF _ pcK nF hfuelF hwfF hwrF hlogF ctx.codeLive hslack hpc
      (hfactsF he) ?_
    intro rv' mv' hpc' hfin hslack'
    exact hcontF he rv' mv' (by rw [hpc', hpcF])
      (fun j hj hj15 => by rw [hfin j hj, hkeepF j hj hj15]) hslack'

/-- The six registers a byte test leaves alone, from six `rfl`s. -/
theorem keepOf (seg : List BBlock) (lds : List (List (BitVec 8))) (rv : Nat → BitVec 64)
    (h1 : finReg seg (strlenL rv) lds 1 = rv 1)
    (h10 : finReg seg (strlenL rv) lds 10 = rv 10)
    (h11 : finReg seg (strlenL rv) lds 11 = rv 11)
    (h12 : finReg seg (strlenL rv) lds 12 = rv 12)
    (h13 : finReg seg (strlenL rv) lds 13 = rv 13)
    (h14 : finReg seg (strlenL rv) lds 14 = rv 14) :
    ∀ j ∈ strlenRegs, j ≠ 15 → finReg seg (strlenL rv) lds j = rv j := by
  intro j hj hj15
  simp only [strlenRegs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact absurd rfl hj15

/-! ### The `snez` at `0x80006d64`

`sltu` is outside `MKind`, so this one instruction is taken from VSA's
generated observational site (`StrlenSites.site_80006d64`) through
`Inst.AluStep`. -/

/-- The `snez a0,a5` site as one local-run step. -/
theorem snezAluStep (ctx : Ctx live P r len bv) (a5 : BitVec 64) :
    AluStep live 0x80006d64 [(15, DFrac.own 1, a5)] (strlenMR P.toNat len bv) 10
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) a5))) := by
  intro c hok hpc hRR hMR
  have hread := reads_of_foot hok ctx.codeLive hMR
  have hpcσ : c.σ.regs.get? Register.PC = some (0x80006d64#64 : BitVec 64) := by
    obtain ⟨w, hw⟩ := hok.good.PC
    have h : pcVal c.σ = BitVec.ofNat 64 0x80006d64 := hpc
    unfold pcVal at h
    rw [hw] at h ⊢
    exact congrArg some h
  have ha5 : gprGet c.σ 15 = some a5 :=
    gprGet_eq_of_vsaReg hok (by omega) (by omega) (hRR _ List.mem_cons_self)
  obtain ⟨vm, hvm⟩ := hok.good.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d64 c.σ c.tick c.steps (0x80006d64#64) vm a5 hok.good hpcσ hvm ha5
      hread.loaded rfl hok.tick
  have hframe := StepFrameOut.of_alu hobs
  have hnoise : ∀ n, n < 32 → 1 ≤ n → ∀ R ∈ noiseRegs, (R == gprReg n) = false := by decide
  have hgprFrame : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ 10 → gprGet σ' n = gprGet c.σ n := by
    intro n h1 h31 hn
    refine gprGet_of_frame (wrs := [10]) n h1 h31 (hnoise n (by omega) h1)
      (fun mm hmm => ?_) (fun R hR hw => hframe.frame R fun rr hrr => ?_)
    · rcases List.mem_cons.mp hmm with rfl | hmm
      · exact gprReg_beq_false 10 (by omega) n (by omega) (by omega) h1 (fun e => hn e.symm)
      · cases hmm
    · rcases List.mem_cons.mp hrr with rfl | hrr
      · exact hw 10 List.mem_cons_self
      · exact hR rr hrr
  have ha0' : σ'.regs.get? Register.x10
      = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) a5))) :=
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨⟨σ', i', c.steps + 1⟩, hstep, ⟨hG', hi', fun n h1 h31 => ?_, fun a ha => ?_, ?_⟩,
    ?_, ?_, ?_, fun a => ?_, ?_⟩
  · show (gprGet σ' n).isSome = true
    by_cases hn : n = 10
    · subst hn
      rw [show gprGet σ' 10 = σ'.regs.get? Register.x10 from rfl, ha0']
      rfl
    · rw [hgprFrame n h1 h31 hn]; exact hok.gpr n h1 h31
  · change (σ'.mem[a]?).isSome
    rw [hmem']; exact hok.live a ha
  · rw [hframe.frame Register.htif_payload_writes (by decide)]; exact hok.htifIdle
  · change pcVal σ' = _
    unfold pcVal
    rw [obs_alu_pc hobs]
    rfl
  · change vsaReg ⟨σ', i', c.steps + 1⟩ 10 = _
    rw [vsaReg_gpr (by decide)]
    change (gprGet σ' 10).getD 0 = _
    rw [show gprGet σ' 10 = σ'.regs.get? Register.x10 from rfl, ha0']
    rfl
  · intro k hkpc hk10
    change vsaReg ⟨σ', i', c.steps + 1⟩ k = vsaReg c k
    rw [vsaReg_gpr hkpc, vsaReg_gpr (c := c) hkpc]
    by_cases hr : 1 ≤ k ∧ k ≤ 31
    · rw [hgprFrame k hr.1 hr.2 hk10]
    · rw [gprGet_none (by unfold VsaIris.PC at hkpc; omega),
        gprGet_none (by unfold VsaIris.PC at hkpc; omega)]
  · change (σ'.mem[a]?).getD 0 = ((c.σ.mem)[a]?).getD 0
    rw [hmem']
  · show Vsa.Machine.output σ' = Vsa.Machine.output c.σ
    unfold Vsa.Machine.output
    rw [hframe.out]

end Run

end VsaIris.Inst.Strlen

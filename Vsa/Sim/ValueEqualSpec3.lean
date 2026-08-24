import Vsa.Sim.ValueEqualSpec2
import Vsa.Sim.ValueEqualSites3
import Vsa.Sim.StrcmpSpecW4
import Vsa.Sim.ValueSpec
import Vsa.Sim.EnvDefSpec2

/-!
# Layer 3 — total-correctness spec for the `str`-`str` handler of `value_equal`

The final `value_equal` handler: `str`-`str` (`@0x800028c4`). Unlike the five non-`str`
handlers (all read-only, `mem = m0` post), this one has a **stack footprint** — it spills
`ra` at `[entry_sp-8, entry_sp)`, calls `strcmp`, restores `ra`, and returns. So at the
return `mem ≠ m0` (the spilled `ra` remains in the scratch slot), and the postcondition is
framed to agree with `m0` **outside** the stack window `[entry_sp-8, entry_sp)`.

## What the handler does

```
0x800028c4  ld a1,8(a1)      ; a1 := pb  (string ptr b, from ValueRepr .str)
0x800028c8  ld a0,8(a0)      ; a0 := pa  (string ptr a)
0x800028cc  addi sp,sp,-16   ; sp := entry_sp - 16
0x800028d0  sd ra,8(sp)      ; spill ra (= r) at (entry_sp-16)+8 = entry_sp-8
0x800028d4  jal strcmp       ; ra := 0x800028d8; PC := strcmp entry (0x80006ea0)
0x800028d8  ld ra,8(sp)      ; restore ra := r from the (untouched) spill slot
0x800028dc  seqz a0,a0       ; a0 := (strcmp result == 0) ? 1 : 0
0x800028e0  addi sp,sp,16    ; sp := entry_sp
0x800028e4  ret              ; PC := r
```

## Result bridge (`x10 == 0 ↔ sa = sb`)

`strcmp_full_spec` returns `strcmpSign x10 = strcmpSpecSign csa csb` where `sa = ofList csa`,
`sb = ofList csb`. `strcmpSign x = 0 ↔ x = 0` (definition), and (under the two `CStr`
witnesses) `strcmpSpecSign csa csb = 0 ↔ sa = sb` (`string_eq_iff_strcmpSpecSign_zero`,
reproved locally). Hence `(x10 == 0) = (sa == sb) = Value.equal (.str sa) (.str sb)`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Value NativeFn)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Spec-sign ↔ string-equality bridge

Reuses `string_eq_iff_strcmpSpecSign_zero` (proved in `EnvDefSpec2`): under two `CStr`
witnesses, `strcmpSpecSign csa csb = 0 ↔ sa = sb`. -/

/-- `CStr` is functional in memory: the char list at an address is unique. Used to lift a
single concrete `StrcmpRegion`/`StrcmpWRegion` witness to strcmp's `∀ cs, CStr … → …`
region family (any `cs` at the pointer equals the witnessed one). -/
theorem cstr_functional (m : Mem) (p : Nat) (cs cs' : List Char)
    (h : CStr m p cs) (h' : CStr m p cs') : cs = cs' := by
  induction h generalizing cs' with
  | @nil a hnil =>
    cases h' with
    | nil _ => rfl
    | @cons a' b' cs'' hb' hbne' hblt' hrest' =>
      rw [hnil] at hb'; injection hb' with hb'; exact absurd hb'.symm hbne'
  | @cons a b cs hb hbne hblt hrest ih =>
    cases h' with
    | nil hnil' => rw [hnil'] at hb; injection hb with hb; exact absurd hb.symm hbne
    | @cons a' b'' cs'' hb'' hbne'' hblt'' hrest'' =>
      rw [hb''] at hb; injection hb with hb; subst hb
      rw [ih cs'' hrest'']

/-! ## `strcmpSign x = 0 ↔ x = 0`. -/
theorem strcmpSign_zero_iff (x : BitVec 64) : strcmpSign x = 0 ↔ x = 0#64 := by
  unfold strcmpSign
  constructor
  · intro h
    by_cases hx : x = 0#64
    · exact hx
    · exfalso
      split at h
      · exact hx (by assumption)
      · split at h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
  · intro h; subst h; rfl

/-! ## `StrcmpLoaded` / `MaskPinned` transfer through an agreeing memory -/

/-- `StrcmpLoaded` transfers to any memory agreeing on the strcmp code region
`[0x80006ea0, 0x80006fcc)`. -/
theorem strcmpLoaded_of_agree (m1 m2 : Std.ExtHashMap Nat (BitVec 8))
    (hagree : ∀ a, 0x80006ea0 ≤ a → a < 0x80006fcc → m2[a]? = m1[a]?)
    (h : StrcmpLoaded m1) : StrcmpLoaded m2 := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.strcmpChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.strcmpChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.strcmpChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.strcmpChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.strcmpChunk4] at c4 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])

/-- `Value_equalLoaded` transfers to any memory agreeing on the code region
`[0x8000285c, 0x800028fc)`. -/
theorem valueEqualLoaded_of_agree (m1 m2 : Std.ExtHashMap Nat (BitVec 8))
    (hagree : ∀ a, 0x8000285c ≤ a → a < 0x800028fc → m2[a]? = m1[a]?)
    (h : Value_equalLoaded m1) : Value_equalLoaded m2 := by
  obtain ⟨c0, c1, c2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.value_equalChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.value_equalChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.value_equalChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])

/-- `MaskPinned` transfers to any memory agreeing on the mask region `[maskAddr, maskAddr+8)`. -/
theorem maskPinned_of_agree (m1 m2 : Std.ExtHashMap Nat (BitVec 8))
    (hagree : ∀ a, maskAddr ≤ a → a < maskAddr + 8 → m2[a]? = m1[a]?)
    (h : MaskPinned m1) : MaskPinned m2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hagree maskAddr (by omega) (by omega)]; exact h0
  · rw [hagree (maskAddr + 1) (by omega) (by omega)]; exact h1
  · rw [hagree (maskAddr + 2) (by omega) (by omega)]; exact h2
  · rw [hagree (maskAddr + 3) (by omega) (by omega)]; exact h3
  · rw [hagree (maskAddr + 4) (by omega) (by omega)]; exact h4
  · rw [hagree (maskAddr + 5) (by omega) (by omega)]; exact h5
  · rw [hagree (maskAddr + 6) (by omega) (by omega)]; exact h6
  · rw [hagree (maskAddr + 7) (by omega) (by omega)]; exact h7

/-! ## Small `sp` / spill arithmetic (reproved locally) -/

theorem ve_sp_sub16 (sp : BitVec 64) :
    (sp + sign_extend (m := 64) (0xff0#12)) = sp - 16#64 := by
  have hs : (sign_extend (m := 64) (0xff0#12) : BitVec 64) = -(16#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have hn : (-(16#64) : BitVec 64).toNat = 2^64 - 16 := by decide
  have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
  rw [hn, h16]; have := sp.isLt; omega

theorem ve_sp_restore (sp : BitVec 64) :
    (sp - 16#64) + sign_extend (m := 64) (0x010#12) = sp := by
  have hs : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
  rw [h16]; have := sp.isLt; omega

theorem ve_sp_sub16_toNat (sp : BitVec 64) (h : 16 ≤ sp.toNat) :
    (sp - 16#64).toNat = sp.toNat - 16 := by
  have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
  rw [BitVec.toNat_sub, h16]; have := sp.isLt; omega

theorem ve_off8 (base : BitVec 64) (h : base.toNat + 8 < 2^64) :
    (base + sign_extend (m := 64) (0x008#12)).toNat = base.toNat + 8 := by
  have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
  rw [BitVec.toNat_add, hs]; omega

/-! ## Stack / disjointness bundle for the `str` handler

`entry_sp` is the entry stack pointer; the spill lives at `[entry_sp-16, entry_sp)` (the
`ra` at `entry_sp-8`). The stack window must be disjoint from the two string byte ranges,
the `strcmp` code, the mask rodata, RAM/HTIF, and be 8-aligned in RAM. -/
structure VEStrRegions (sp : BitVec 64) (pa pb : Nat) (la lb : Nat) : Prop where
  /-- ≥ 16 bytes of stack. -/
  sp16 : 16 ≤ sp.toNat
  /-- the spilled dword window `[entry_sp-16, entry_sp)` is in RAM. -/
  win_lo : 0x80000000 ≤ sp.toNat - 16
  win_hi : sp.toNat ≤ 0x100000000
  /-- above the HTIF window. -/
  win_htif : tohostAddr + 16 ≤ sp.toNat - 16
  /-- 8-aligned scratch frame. -/
  win_align : (sp.toNat - 16) % 8 = 0
  /-- disjoint from string A's byte range `[pa, pa+la]`. -/
  str_a : sp.toNat ≤ pa ∨ pa + la + 1 ≤ sp.toNat - 16
  /-- disjoint from string B's byte range `[pb, pb+lb]`. -/
  str_b : sp.toNat ≤ pb ∨ pb + lb + 1 ≤ sp.toNat - 16
  /-- disjoint from the strcmp code `[0x80006ea0, 0x80006fcc)`. -/
  code : sp.toNat ≤ 0x80006ea0 ∨ 0x80006fcc ≤ sp.toNat - 16
  /-- disjoint from the mask rodata `[maskAddr, maskAddr+8)`. -/
  mask : sp.toNat ≤ maskAddr ∨ maskAddr + 8 ≤ sp.toNat - 16
  /-- disjoint from the `value_equal` code `[0x8000285c, 0x800028fc)`. -/
  vecode : sp.toNat ≤ 0x8000285c ∨ 0x800028fc ≤ sp.toNat - 16

/-- Fold the 8 spilled `sdData_val v` bytes back to `v` under the `ld`. -/
theorem ve_sext_reassemble (v : BitVec 64) :
    (sign_extend (m := 64)
      (((((((((sdData_val v).extractLsb' 56 8).append ((sdData_val v).extractLsb' 48 8)).append
        ((sdData_val v).extractLsb' 40 8)).append ((sdData_val v).extractLsb' 32 8)).append
        ((sdData_val v).extractLsb' 24 8)).append ((sdData_val v).extractLsb' 16 8)).append
        ((sdData_val v).extractLsb' 8 8)).append ((sdData_val v).extractLsb' 0 8)
        : BitVec (8 * 8)) : BitVec 64) = v := by
  rw [sext_full]
  apply BitVec.eq_of_toNat_eq
  rw [word8_toNat_recon]
  have hv : (sdData_val v).toNat = v.toNat := sdData_toNat v
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, hv]
  have := v.isLt
  omega

/-- `read64` is unaffected by a disjoint `writeMap8`. -/
theorem ve_read64_writeMap8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8 mem a8 d) a = read64 mem a := by
  have g0 := getElem_writeMap8_disjoint mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega)
  have g4 := getElem_writeMap8_disjoint mem a8 (a + 4) d (by omega)
  have g5 := getElem_writeMap8_disjoint mem a8 (a + 5) d (by omega)
  have g6 := getElem_writeMap8_disjoint mem a8 (a + 6) d (by omega)
  have g7 := getElem_writeMap8_disjoint mem a8 (a + 7) d (by omega)
  simp only [read64, readLE, g0, g1, g2, g3, g4, g5, g6, g7]

/-! ## Str-path ghost frame

The `str` handler additionally writes `x1` (`ra`: spill `ld`, `jal` link) and `x2` (`sp`:
two `addi`), both restored to their entry values by return. Mid-computation these differ
from the entry ghost, so they are threaded explicitly; `NotWrittenVEStr` excludes them (and
strcmp's caller-saved scratch `x5-x7`, `x12-x15`) so the blanket frame carries every other
register through the whole handler including the callee. -/
abbrev NotWrittenVEStr (R : Register) : Prop :=
  (Register.x1 == R) = false ∧ (Register.x2 == R) = false ∧
  (Register.x5 == R) = false ∧ (Register.x6 == R) = false ∧ (Register.x7 == R) = false ∧
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧ (Register.x12 == R) = false ∧
  (Register.x13 == R) = false ∧ (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-- `NotWrittenVEStr R` gives the `NotWrittenStrcmp R` disequalities (strcmp's write-set
`⊆` the str-path write-set), so the str frame carries through the `strcmp` call. -/
theorem notWrittenStrcmp_of_str {R : Register} (h : NotWrittenVEStr R) : NotWrittenStrcmp R := by
  obtain ⟨_, _, hx5, hx6, hx7, hx10, hx11, hx12, hx13, hx14, hx15, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := h
  exact ⟨hx5, hx6, hx7, hx10, hx11, hx12, hx13, hx14, hx15, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩

/-- `NotWrittenVEStr R → NotWrittenVE R` (the str write-set is a superset). -/
theorem notWrittenVE_of_str {R : Register} (h : NotWrittenVEStr R) : NotWrittenVE R := by
  obtain ⟨_, _, _, _, _, hx10, _, _, _, hx14, hx15, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := h
  exact ⟨hx10, hx14, hx15, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩

/-- ALU frame step under the str frame (`rd ∈ str write-set` supplied by the caller). -/
theorem frame_alu_vestr {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hR : NotWrittenVEStr R) (hrd : (rd == R) = false) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

/-- STORE frame step under the str frame. -/
theorem frame_store_vestr {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenVEStr R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

/-- `jal` frame step under the str frame (link `rd = x1`, excluded by `hR.1`). -/
theorem frame_jal_vestr {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register)
    (hR : NotWrittenVEStr R) (hrd : (rd_reg == R) = false) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jal σ pc vm imm rd_reg link R hmi hpc hrd hnpc hmii

/-- `jr`/`ret` frame step under the str frame. -/
theorem frame_jr_vestr {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenVEStr R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## `jal` observation consumers (inlined, analogue of `obs_alu_*`)

Copied from `DivSites2`/`EnvNewSpec` (which we do not import — heavy dependencies). From a
`jal` observation, read the framing fields off `σ'`. -/

theorem ve_post_jal_pc (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.PC
      = some (pc + sign_extend (m := 64) imm) := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem ve_post_jal_rd (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? rd_reg = some link := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
    (pc + sign_extend (m := 64) imm)).insert rd_reg link).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem ve_obs_jal_pc {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (ve_post_jal_pc σ pc vm imm rd_reg link)

theorem ve_obs_jal_rd {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi (ve_post_jal_rd σ pc vm imm rd_reg link h1 h2)

theorem ve_obs_jal_other {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_jal σ pc vm imm rd_reg link R h1 h2 h3 h4 h5).trans hσ)

theorem ve_obs_jal_minstret {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## The `str`-`str` handler up to the `strcmp` result (`0x800028c4 → 0x800028d8`)

### ARCHITECTURAL BLOCKER (epilogue unreachable against the current `strcmp` spec)

The str handler spills `ra`, calls `strcmp`, then runs the epilogue `ld ra,8(sp); seqz;
addi sp,sp,16; ret`.  The epilogue's effective addresses (`ld`/`addi` off `sp`) and the
final `ret` target all require knowing `x2 = sp - 16` **after** the call — but
`strcmp_post` (`StrcmpSpec.lean:1038`) exposes **no register/`sp`/ghost frame at all**
(only `PC = r`, `x1 = r`, `x10`, `mem = m0`, `tick`, `GoodState`).  So `sp` (and every
callee-saved GPR) is lost across the call, and the epilogue cannot be threaded.  Extending
`strcmp_post` with a `NotWrittenStrcmp` blanket frame (as its own docstring at line 1070
*claims* but does not carry) is the prerequisite; that requires editing `StrcmpSpec.lean`,
which is out of scope here.

What IS provable — and proved below — is the run **through the `strcmp` call**: the spill,
the callee-contract composition (`strcmp_full_spec`, all witnesses transferred through the
spill via `cstr_writeMap8_disjoint` / `strcmpLoaded_of_agree` / `maskPinned_of_agree` /
`valueEqualLoaded_of_agree`), and the result bridge to `Value.equal (.str sa) (.str sb)`.

`ve_str_reaches_result`: from `0x800028c4` to the `strcmp` return `0x800028d8`, with
`x10`'s value being the machine `strcmp` result whose `== 0` test decides `sa = sb`, and
`mem = m1` (the spilled memory, agreeing with `m0` off the stack window). -/
theorem ve_str_reaches_result
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (sa sb : String) (pa' pb' : Nat) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0) (hloaded : Value_equalLoaded m0)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0)
    (hpc : σ.regs.get? Register.PC = some (0x800028c4#64 : BitVec 64))
    (ha0 : σ.regs.get? Register.x10 = some bufa) (ha1 : σ.regs.get? Register.x11 = some bufb)
    (hra : σ.regs.get? Register.x1 = some r) (hsp : σ.regs.get? Register.x2 = some sp)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hrega : VERegion bufa) (hregb : VERegion bufb)
    (_hralign : r.toNat % 4 = 0)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R)
    -- the two string payloads (from `ValueRepr .str`)
    (hpa : read64 m0 (bufa.toNat + 8) = some pa') (hpb : read64 m0 (bufb.toNat + 8) = some pb')
    (hca : CStr m0 pa' csa) (hcb : CStr m0 pb' csb)
    (hsa : sa = String.ofList csa) (hsb : sb = String.ofList csb)
    -- strcmp region families (over `m0`; the specific `csa`/`csb` witnesses suffice)
    (hbra : StrcmpRegion (BitVec.ofNat 64 pa') csa.length)
    (hbrb : StrcmpRegion (BitVec.ofNat 64 pb') csb.length)
    (hwra : StrcmpWRegion (BitVec.ofNat 64 pa') csa.length)
    (hwrb : StrcmpWRegion (BitVec.ofNat 64 pb') csb.length)
    -- stack / disjointness bundle
    (hSR : VEStrRegions sp pa' pb' csa.length csb.length) :
    ∃ (c6 : Config) (m1 : Std.ExtHashMap Nat (BitVec 8)) (x : BitVec 64),
      Steps c c6 ∧ GoodState c6.σ ∧ c6.tick < 2 ∧
      c6.σ.regs.get? Register.PC = some (0x800028d8#64 : BitVec 64) ∧
      c6.σ.regs.get? Register.x1 = some (0x800028d8#64 : BitVec 64) ∧
      c6.σ.regs.get? Register.x10 = some x ∧
      -- the `== 0` result test decides `Value.equal (.str sa) (.str sb)`:
      ((x == 0#64) = Value.equal (.str sa) (.str sb)) ∧
      -- `sp` is recovered across the call via strcmp's ghost frame (`x2 ∉ write-set`):
      c6.σ.regs.get? Register.x2 = some (sp - 16#64) ∧
      c6.σ.mem = m1 ∧
      (∀ a, ¬ (sp.toNat - 16 ≤ a ∧ a < sp.toNat) → m1[a]? = m0[a]?) ∧
      -- the whole `NotWrittenVEStr` frame carries back to the handler-entry ghost `g`
      -- (strcmp's frame ∘ the pre-call str frame); the epilogue consumes this.
      (∀ R : Register, NotWrittenVEStr R → c6.σ.regs.get? R = g R) ∧
      -- the concrete spilled-memory form (for the epilogue's `ld ra` slot readback) and its
      -- `Value_equalLoaded`:
      m1 = writeMap8 m0 ((sp - 16#64).toNat + 8) (sdData_val r) ∧
      Value_equalLoaded m1 := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- byte reconstructions of the two payload loads
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hab0, hab1, hab2, hab3, hab4, hab5, hab6, hab7, harec⟩ :=
    read64_bytes m0 (bufa.toNat + 8) _ hpa
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, hdb0, hdb1, hdb2, hdb3, hdb4, hdb5, hdb6, hdb7, hdrec⟩ :=
    read64_bytes m0 (bufb.toNat + 8) _ hpb
  obtain ⟨hlo_a, hhi_a, hhtif_a, halign_a⟩ := ve_pay8_bounds bufa hrega
  obtain ⟨hlo_b, hhi_b, hhtif_b, halign_b⟩ := ve_pay8_bounds bufb hregb
  -- === 0x800028c4: ld a1,8(a1) ⇒ x11 := ofNat pb' ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800028c4 σ i steps0 (0x800028c4#64) vmi bufb d0 d1 d2 d3 d4 d5 d6 d7
      hG hpc hmi ha1 (hmem ▸ hloaded) rfl hlo_b hhi_b hhtif_b halign_b
      (by rw [ve_pay8_addr bufb hregb, hmem]; exact hdb0) (by rw [ve_pay8_addr bufb hregb, hmem]; exact hdb1)
      (by rw [ve_pay8_addr bufb hregb, hmem]; exact hdb2) (by rw [ve_pay8_addr bufb hregb, hmem]; exact hdb3)
      (by rw [ve_pay8_addr bufb hregb, hmem]; exact hdb4) (by rw [ve_pay8_addr bufb hregb, hmem]; exact hdb5)
      (by rw [ve_pay8_addr bufb hregb, hmem]; exact hdb6) (by rw [ve_pay8_addr bufb hregb, hmem]; exact hdb7) hi
  have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some (0x800028c8#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800028c4#64) 4 = (0x800028c8#64 : BitVec 64) from by decide] at this
  have ha1_1 : σ1.regs.get? Register.x11 = some (BitVec.ofNat 64 pb') := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, ld_sext_ofNat d0 d1 d2 d3 d4 d5 d6 d7 pb' hdrec]
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have hsp_1 := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframestr : ∀ R : Register, NotWrittenVEStr R → σ.regs.get? R = g R :=
    fun R hR => hframe R (notWrittenVE_of_str hR)
  have hframe1 : ∀ R : Register, NotWrittenVEStr R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_vestr hobs1 R hR hR.2.2.2.2.2.2.1).trans (hframestr R hR)
  -- === 0x800028c8: ld a0,8(a0) ⇒ x10 := ofNat pa' ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800028c8 σ1 i1 (steps0 + 1) (0x800028c8#64) vmi1 bufa a0 a1 a2 a3 a4 a5 a6 a7
      hG1 hpc1 hmi1 ha0_1 (hmem1eq ▸ hloaded) rfl hlo_a hhi_a hhtif_a halign_a
      (by rw [ve_pay8_addr bufa hrega, hmem1eq]; exact hab0) (by rw [ve_pay8_addr bufa hrega, hmem1eq]; exact hab1)
      (by rw [ve_pay8_addr bufa hrega, hmem1eq]; exact hab2) (by rw [ve_pay8_addr bufa hrega, hmem1eq]; exact hab3)
      (by rw [ve_pay8_addr bufa hrega, hmem1eq]; exact hab4) (by rw [ve_pay8_addr bufa hrega, hmem1eq]; exact hab5)
      (by rw [ve_pay8_addr bufa hrega, hmem1eq]; exact hab6) (by rw [ve_pay8_addr bufa hrega, hmem1eq]; exact hab7) hi1
  have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x800028cc#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800028c8#64) 4 = (0x800028cc#64 : BitVec 64) from by decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some (BitVec.ofNat 64 pa') := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, ld_sext_ofNat a0 a1 a2 a3 a4 a5 a6 a7 pa' harec]
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hsp_2 := obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenVEStr R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_vestr hobs2 R hR hR.2.2.2.2.2.1).trans (hframe1 R hR)
  -- === 0x800028cc: addi sp,sp,-16 ⇒ x2 := sp - 16 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800028cc σ2 i2 (steps0 + 1 + 1) (0x800028cc#64) vmi2 sp hG2 hpc2 hmi2 hsp_2 (hmem2eq ▸ hloaded) rfl hi2
  have hmem3eq : σ3.mem = m0 := by rw [hmem3, hmem2eq]
  have hpc3 : σ3.regs.get? Register.PC = some (0x800028d0#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800028cc#64) 4 = (0x800028d0#64 : BitVec 64) from by decide] at this
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 16#64) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sp_sub16 sp] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hframe3 : ∀ R : Register, NotWrittenVEStr R → σ3.regs.get? R = g R := fun R hR =>
    (frame_alu_vestr hobs3 R hR hR.2.1).trans (hframe2 R hR)
  -- spn facts
  have hspn_toNat : (sp - 16#64).toNat = sp.toNat - 16 := ve_sp_sub16_toNat sp hSR.sp16
  have hspn8 : ((sp - 16#64) + sign_extend (m := 64) (0x008#12)).toNat = (sp - 16#64).toNat + 8 := by
    apply ve_off8; rw [hspn_toNat]; have := sp.isLt; omega
  -- === 0x800028d0: sd ra,8(sp) ⇒ mem += (r @ spn+8) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_800028d0 σ3 i3 (steps0 + 1 + 1 + 1) (0x800028d0#64) vmi3 (sp - 16#64) r
      hG3 hpc3 hmi3 hsp_3 hra_3 (hmem3eq ▸ hloaded) rfl
      (by rw [hspn8, hspn_toNat]; have := hSR.win_lo; omega)
      (by rw [hspn8, hspn_toNat]; have := hSR.win_hi; omega)
      (by rw [hspn8, hspn_toNat]; have := hSR.win_htif; omega)
      (by rw [hspn8, hspn_toNat]; have := hSR.win_align; omega) hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x800028d4#64 : BitVec 64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x800028d0#64) 4 = (0x800028d4#64 : BitVec 64) from by decide] at this
  have hsp_4 := obs_store_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  have ha0_4 := obs_store_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 := obs_store_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
  have hra_4 := obs_store_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  -- σ4.mem = writeMap8 m0 (spn+8) r  (=: m1, the spilled memory)
  have hmem4' : σ4.mem = writeMap8 m0 ((sp - 16#64).toNat + 8) (sdData_val r) := by
    rw [hmem4, mem_afterNextPC, hmem3eq, hspn8]
  let m1 := writeMap8 m0 ((sp - 16#64).toNat + 8) (sdData_val r)
  have hm1def : m1 = writeMap8 m0 ((sp - 16#64).toNat + 8) (sdData_val r) := rfl
  have hframe4 : ∀ R : Register, NotWrittenVEStr R → σ4.regs.get? R = g R := fun R hR =>
    (frame_store_vestr hobs4 R hR).trans (hframe3 R hR)
  -- the spill window `[spn+8, spn+16) = [sp-8, sp)` is disjoint from strings / mask / code
  have hspn8_nat : (sp - 16#64).toNat + 8 = sp.toNat - 8 := by rw [hspn_toNat]; have := hSR.sp16; omega
  have hstr_a_dis : (sp - 16#64).toNat + 8 + 8 ≤ pa' ∨ pa' + csa.length < (sp - 16#64).toNat + 8 := by
    rw [hspn_toNat]; have := hSR.sp16; rcases hSR.str_a with h | h
    · left; omega
    · right; omega
  have hstr_b_dis : (sp - 16#64).toNat + 8 + 8 ≤ pb' ∨ pb' + csb.length < (sp - 16#64).toNat + 8 := by
    rw [hspn_toNat]; have := hSR.sp16; rcases hSR.str_b with h | h
    · left; omega
    · right; omega
  -- string / loaded / mask witnesses transfer through the spill into `m1`
  have hca1 : CStr m1 pa' csa := by
    rw [hm1def]; exact cstr_writeMap8_disjoint m0 _ pa' _ csa hca hstr_a_dis
  have hcb1 : CStr m1 pb' csb := by
    rw [hm1def]; exact cstr_writeMap8_disjoint m0 _ pb' _ csb hcb hstr_b_dis
  -- `m1` agrees with `m0` off the spill window `[spn+8, spn+16)`
  have hagree1 : ∀ a, ¬ ((sp - 16#64).toNat + 8 ≤ a ∧ a < (sp - 16#64).toNat + 8 + 8) → m1[a]? = m0[a]? := by
    intro a ha
    rw [hm1def, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
  have hstrc1 : StrcmpLoaded m1 :=
    strcmpLoaded_of_agree m0 m1 (fun a hlo hhi => hagree1 a (by
      rw [hspn8_nat]; rcases hSR.code with h | h
      · exact fun ⟨_, h2⟩ => by omega
      · exact fun ⟨h1, _⟩ => by omega)) hstrc
  have hmask1 : MaskPinned m1 :=
    maskPinned_of_agree m0 m1 (fun a hlo hhi => hagree1 a (by
      rw [hspn8_nat]; rcases hSR.mask with h | h
      · exact fun ⟨_, h2⟩ => by omega
      · exact fun ⟨h1, _⟩ => by omega)) hmask
  have hloaded1 : Value_equalLoaded m1 :=
    valueEqualLoaded_of_agree m0 m1 (fun a hlo hhi => hagree1 a (by
      rw [hspn8_nat]; rcases hSR.vecode with h | h
      · exact fun ⟨_, h2⟩ => by omega
      · exact fun ⟨h1, _⟩ => by omega)) hloaded
  -- CString wrappers for strcmp's precondition
  have hcstra1 : CString m1 (BitVec.ofNat 64 pa').toNat sa := by
    have hpn : (BitVec.ofNat 64 pa').toNat = pa' := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hbra.hi; omega)]
    rw [hpn]; exact ⟨csa, hca1, hsa⟩
  have hcstrb1 : CString m1 (BitVec.ofNat 64 pb').toNat sb := by
    have hpn : (BitVec.ofNat 64 pb').toNat = pb' := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hbrb.hi; omega)]
    rw [hpn]; exact ⟨csb, hcb1, hsb⟩
  have hmem4eq1 : σ4.mem = m1 := by rw [hmem4', hm1def]
  -- === 0x800028d4: jal strcmp ⇒ x1 := 0x800028d8, PC := strcmp entry ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_800028d4 σ4 i4 (steps0 + 1 + 1 + 1 + 1) (0x800028d4#64) vmi4 hG4 hpc4 hmi4
      (hmem4eq1 ▸ hloaded1) rfl hi4
  have hmem5eq : σ5.mem = m1 := by rw [hmem5, hmem4eq1]
  have hpc5 : σ5.regs.get? Register.PC = some (BitVec.ofNat 64 0x80006ea0) := by
    have := ve_obs_jal_pc hobs5
    rwa [show (0x800028d4#64 : BitVec 64) + sign_extend (m := 64) (0x0045cc#21)
      = (BitVec.ofNat 64 0x80006ea0) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hra_5 : σ5.regs.get? Register.x1 = some (0x800028d8#64) := by
    have := ve_obs_jal_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800028d4#64 : BitVec 64) 4 = (0x800028d8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha0_5 := ve_obs_jal_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have ha1_5 := ve_obs_jal_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_4
  have hsp_5 := ve_obs_jal_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_4
  obtain ⟨vmi5, hmi5⟩ := ve_obs_jal_minstret hobs5
  -- str frame through the jal (link `rd = x1`)
  have hframe5 : ∀ R : Register, NotWrittenVEStr R → σ5.regs.get? R = g R := fun R hR =>
    (frame_jal_vestr hobs5 R hR hR.1).trans (hframe4 R hR)
  -- pointer facts for the two `ofNat` string pointers
  have hpa_nat : (BitVec.ofNat 64 pa').toNat = pa' := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hbra.hi; omega)]
  have hpb_nat : (BitVec.ofNat 64 pb').toNat = pb' := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hbrb.hi; omega)]
  -- === strcmp call (contract `strcmp_full_spec`) ===
  -- ghost at the callee entry state `σ5`, so the frame tie is `rfl`.
  have ha0_5' : σ5.regs.get? Register.x10 = some (BitVec.ofNat 64 pa') := ha0_5
  have hca1' : CStr m1 (BitVec.ofNat 64 pa').toNat csa := by rw [hpa_nat]; exact hca1
  have hcb1' : CStr m1 (BitVec.ofNat 64 pb').toNat csb := by rw [hpb_nat]; exact hcb1
  have hcorepre : strcmp_full_pre (fun R => σ5.regs.get? R) (BitVec.ofNat 64 pa')
      (BitVec.ofNat 64 pb') (0x800028d8#64) sa sb m1 ⟨σ5, i5, steps0 + 1 + 1 + 1 + 1 + 1⟩ := by
    refine ⟨hG5, hmem5eq ▸ hstrc1, hmem5eq, ?_, ha0_5', ha1_5, hra_5,
      ⟨vmi5, hmi5⟩, hi5, (by decide), hcstra1, hcstrb1, hmem5eq ▸ hmask1,
      (fun cs hcs => cstr_functional m1 _ cs csa hcs hca1' ▸ hbra),
      (fun cs hcs => cstr_functional m1 _ cs csb hcs hcb1' ▸ hbrb),
      (fun cs hcs => cstr_functional m1 _ cs csa hcs hca1' ▸ hwra),
      (fun cs hcs => cstr_functional m1 _ cs csb hcs hcb1' ▸ hwrb), fun R _ => rfl⟩
    rw [hpc5]
  obtain ⟨c6, hs6, hpost6⟩ :=
    strcmp_full_spec (fun R => σ5.regs.get? R) (BitVec.ofNat 64 pa') (BitVec.ofNat 64 pb')
      (0x800028d8#64) sa sb m1 ⟨σ5, i5, steps0 + 1 + 1 + 1 + 1 + 1⟩ hcorepre
  -- strcmp post: returned to 0x800028d8, mem = m1, x10's sign the spec sign
  obtain ⟨hG6, hpc6, hra6, hmem6, htick6, hframe6, csa', csb', x10v, hca6, hcb6, hsa6, hsb6, hx10_6, hsign6⟩ := hpost6
  -- recover `sp` across the call: `x2 ∉ NotWrittenStrcmp`'s write-set, so the ghost frame ties
  -- `c6.σ.regs.get? x2` back to `σ5.regs.get? x2 = sp - 16`.
  have hsp6 : c6.σ.regs.get? Register.x2 = some (sp - 16#64) :=
    (hframe6 Register.x2 (by decide)).trans hsp_5
  -- the char lists strcmp saw are the same (CStr functional on m1)
  have hcsa_eq : csa' = csa := cstr_functional m1 _ csa' csa (by rw [hpa_nat] at hca6; exact hca6) hca1
  have hcsb_eq : csb' = csb := cstr_functional m1 _ csb' csb (by rw [hpb_nat] at hcb6; exact hcb6) hcb1
  rw [hcsa_eq, hcsb_eq] at hsign6
  -- === RESULT BRIDGE: (x10v == 0) = Value.equal (.str sa) (.str sb) ===
  have hval : Value.equal (.str sa) (.str sb) = (sa == sb) := rfl
  have hbridge : (x10v == 0#64) = Value.equal (.str sa) (.str sb) := by
    rw [hval]
    by_cases heq : sa = sb
    · -- equal strings ⇒ spec sign 0 ⇒ strcmpSign 0 ⇒ x10v = 0
      have hspec0 : strcmpSpecSign csa csb = 0 :=
        (string_eq_iff_strcmpSpecSign_zero m1 (BitVec.ofNat 64 pa').toNat
          (BitVec.ofNat 64 pb').toNat sa sb csa csb (by rw [hpa_nat]; exact hca1)
          (by rw [hpb_nat]; exact hcb1) hsa hsb).mpr heq
      have hx0 : x10v = 0#64 := (strcmpSign_zero_iff x10v).mp (by rw [hsign6, hspec0])
      rw [hx0]; simp only [beq_self_eq_true]
      exact (beq_iff_eq.mpr heq).symm ▸ rfl
    · -- unequal strings ⇒ spec sign ≠ 0 ⇒ x10v ≠ 0
      have hspecne : strcmpSpecSign csa csb ≠ 0 := fun h0 =>
        heq ((string_eq_iff_strcmpSpecSign_zero m1 (BitVec.ofNat 64 pa').toNat
          (BitVec.ofNat 64 pb').toNat sa sb csa csb (by rw [hpa_nat]; exact hca1)
          (by rw [hpb_nat]; exact hcb1) hsa hsb).mp h0)
      have hxne : x10v ≠ 0#64 := fun hx0 => hspecne (by rw [← hsign6, hx0]; rfl)
      rw [show (x10v == 0#64) = false from by simp only [beq_eq_false_iff_ne, ne_eq]; exact hxne,
        show (sa == sb) = false from by simp only [beq_eq_false_iff_ne, ne_eq]; exact heq]
  -- === memory: m1 agrees with m0 off the stack window [sp-16, sp) ===
  have hmem_frame : ∀ a, ¬ (sp.toNat - 16 ≤ a ∧ a < sp.toNat) → m1[a]? = m0[a]? := by
    intro a ha
    rw [hm1def, getElem_writeMap8_disjoint _ _ _ _ (by rw [hspn8_nat]; omega)]
  -- assemble: c → σ5-config → c6
  have hsteps_all : Steps c c6 :=
    (((((hsteps0.trans (Steps.single hs1)).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans hs6
  -- the full VEStr frame at c6: strcmp's frame (over σ5's ghost) ∘ the pre-call str frame
  have hframeStr6 : ∀ R : Register, NotWrittenVEStr R → c6.σ.regs.get? R = g R := fun R hR =>
    (hframe6 R (notWrittenStrcmp_of_str hR)).trans (hframe5 R hR)
  exact ⟨c6, m1, x10v, hsteps_all, hG6, htick6, hpc6, hra6, hx10_6, hbridge, hsp6, hmem6,
    hmem_frame, hframeStr6, hm1def, hloaded1⟩

end Vsa.Sim

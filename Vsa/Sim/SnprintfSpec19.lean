import Vsa.Sim.SsputsSites
import Vsa.Sim.SnprintfSpec18
import Vsa.Sim.EnvDefSpec4
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec19` : the `__ssputs_r` fast path (`_sp`), composed with `memmove`

Total-correctness spec for the `__ssputs_r` fast path (`0x8001438c … 0x800143f0`),
composed with `memmove_fwd_spec` (SnprintfSpec18) at the `jal` site `0x800143c0`.

From the entry with the sink struct pointer `p` in `a1`, the source base `s` in
`a2`, the length `n` (`1 ≤ n ≤ 31`) in `a3`, the cursor `d` pinned at `[p, p+8)`
and the capacity word `cap32` at `[p+12, p+16)` (with `n < sext32 cap32` — the
fast-path guard), the machine runs to `ret` (`PC = r`) with:

* `a0 = 0` (success),
* the `n` source bytes copied to `[d, d+n)`,
* the cursor slot `[p, p+8)` holding `d + n`,
* the capacity slot `[p+12, p+16)` holding the `subw` result `spNewCap cap32 n`,
* callee-saved `s0/s1/sp` restored (`v8`/`v9`/`vsp`), and
* all memory outside `[d,d+n) ∪ [p,p+8) ∪ [p+12,p+16) ∪ [vsp-24,vsp)` unchanged.

The stack frame is 64 bytes (`addi sp,sp,-64`); the three spill slots actually
written are `vsp-24` (`s1`), `vsp-16` (`s0`), `vsp-8` (`ra`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemmoveLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Small value bridges -/

/-- `base + sext 0x00c = base + 12` (no wrap). -/
theorem off_sp_0c (base : BitVec 64) (h : base.toNat + 12 < 2^64) :
    (base + sign_extend (m := 64) (0x00c#12)).toNat = base.toNat + 12 := by
  have hs : (sign_extend (m := 64) (0x00c#12) : BitVec 64).toNat = 12 := by decide
  rw [BitVec.toNat_add, hs]; omega

/-- The 4-byte LE reassembly of the byte slices of a 32-bit word is the word. -/
theorem word4_eq_sp (w : BitVec 32) :
    ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8) : BitVec (8 * 4)) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [word_toNat_recon]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

/-- The `lw` of the 4 pinned `cap32` bytes yields `sext32 cap32`. -/
theorem lw_cap_reassemble_sp (w : BitVec 32) :
    (sign_extend (m := 64)
      ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
        (w.extractLsb' 0 8) : BitVec (8 * 4)) : BitVec 64) = sign_extend (m := 64) w :=
  congrArg _ (word4_eq_sp w)

/-- `sext.w` of `ofNat n + sext 0` is `ofNat n` for small `n`. -/
theorem sextw_ofNat_sp (n : Nat) (h : n < 128) :
    (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((BitVec.ofNat 64 n : BitVec 64) + sign_extend (m := 64) (0x000#12)) 31 0)
      : BitVec 64) = BitVec.ofNat 64 n := by
  rw [sext0_add]
  refine sext_word_small _ n h ?_
  show (BitVec.ofNat (31 - 0 + 1) ((BitVec.ofNat 64 n : BitVec 64).toNat >>> 0)).toNat = n
  rw [Nat.shiftRight_zero, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The `subw` result at `0x800143d0`: `sext32(low32(sext32 cap32) − low32(ofNat n))`
(the new capacity word left in the raw `execute_rtypew_subw_char` value form). -/
def spNewCap (cap32 : BitVec 32) (n : Nat) : BitVec 64 :=
  sign_extend (m := 64)
    ((Sail.BitVec.extractLsb (sign_extend (m := 64) cap32 : BitVec 64) 31 0)
      - (Sail.BitVec.extractLsb (BitVec.ofNat 64 n : BitVec 64) 31 0))

/-! ## Code-region survival (`__ssputs_r` spans `[0x8001438c, 0x80014520)`) -/

theorem getElem?_insert_above_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80014520 ≤ k) (a : Nat) (ha : a < 0x80014520) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem ssputs_insert_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80014520 ≤ k) (h : Vsa.Sim.Code.__ssputs_rLoaded mem) :
    Vsa.Sim.Code.__ssputs_rLoaded (mem.insert k v) := by
  unfold Vsa.Sim.Code.__ssputs_rLoaded Vsa.Sim.Code.__ssputs_rChunk0
    Vsa.Sim.Code.__ssputs_rChunk1 Vsa.Sim.Code.__ssputs_rChunk2 Vsa.Sim.Code.__ssputs_rChunk3
    Vsa.Sim.Code.__ssputs_rChunk4 Vsa.Sim.Code.__ssputs_rChunk5 Vsa.Sim.Code.__ssputs_rChunk6
    at h ⊢
  simp (disch := omega) only [getElem?_insert_above_ss mem k v hk]
  exact h

theorem ssputs_writeMap8_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8))
    (ha : 0x80014520 ≤ a) (h : Vsa.Sim.Code.__ssputs_rLoaded mem) :
    Vsa.Sim.Code.__ssputs_rLoaded (writeMap8 mem a d) :=
  ssputs_insert_ss _ _ _ (by omega) (ssputs_insert_ss _ _ _ (by omega)
    (ssputs_insert_ss _ _ _ (by omega) (ssputs_insert_ss _ _ _ (by omega)
    (ssputs_insert_ss _ _ _ (by omega) (ssputs_insert_ss _ _ _ (by omega)
    (ssputs_insert_ss _ _ _ (by omega) (ssputs_insert_ss _ _ _ (by omega) h)))))))

theorem ssputs_writeMap4_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4))
    (ha : 0x80014520 ≤ a) (h : Vsa.Sim.Code.__ssputs_rLoaded mem) :
    Vsa.Sim.Code.__ssputs_rLoaded (writeMap4 mem a d) :=
  ssputs_insert_ss _ _ _ (by omega) (ssputs_insert_ss _ _ _ (by omega)
    (ssputs_insert_ss _ _ _ (by omega) (ssputs_insert_ss _ _ _ (by omega) h)))

/-- Pointwise low-memory frame (`< 0x80014520`) transports `__ssputs_rLoaded`. -/
theorem ssputs_frame_ss (mem mem' : Std.ExtHashMap Nat (BitVec 8))
    (hf : ∀ a, a < 0x80014520 → mem'[a]? = mem[a]?)
    (h : Vsa.Sim.Code.__ssputs_rLoaded mem) : Vsa.Sim.Code.__ssputs_rLoaded mem' := by
  unfold Vsa.Sim.Code.__ssputs_rLoaded Vsa.Sim.Code.__ssputs_rChunk0
    Vsa.Sim.Code.__ssputs_rChunk1 Vsa.Sim.Code.__ssputs_rChunk2 Vsa.Sim.Code.__ssputs_rChunk3
    Vsa.Sim.Code.__ssputs_rChunk4 Vsa.Sim.Code.__ssputs_rChunk5 Vsa.Sim.Code.__ssputs_rChunk6
    at h ⊢
  simp (disch := omega) only [hf]
  exact h

theorem memmove_writeMap8_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8))
    (ha : 0x80006b00 ≤ a) (h : MemmoveLoaded mem) : MemmoveLoaded (writeMap8 mem a d) :=
  memmove_insert_mv _ _ _ (by omega) (memmove_insert_mv _ _ _ (by omega)
    (memmove_insert_mv _ _ _ (by omega) (memmove_insert_mv _ _ _ (by omega)
    (memmove_insert_mv _ _ _ (by omega) (memmove_insert_mv _ _ _ (by omega)
    (memmove_insert_mv _ _ _ (by omega) (memmove_insert_mv _ _ _ (by omega) h)))))))

/-! ## 8-byte / 4-byte slot pins -/

/-- The 8 little-endian bytes of `sdData_val v` pinned at `[a, a+8)`. -/
def Pin8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) : Prop :=
  mem[a]? = some ((sdData_val v).extractLsb' 0 8) ∧
  mem[a + 1]? = some ((sdData_val v).extractLsb' 8 8) ∧
  mem[a + 2]? = some ((sdData_val v).extractLsb' 16 8) ∧
  mem[a + 3]? = some ((sdData_val v).extractLsb' 24 8) ∧
  mem[a + 4]? = some ((sdData_val v).extractLsb' 32 8) ∧
  mem[a + 5]? = some ((sdData_val v).extractLsb' 40 8) ∧
  mem[a + 6]? = some ((sdData_val v).extractLsb' 48 8) ∧
  mem[a + 7]? = some ((sdData_val v).extractLsb' 56 8)

/-- The 4 little-endian bytes of a 32-bit word pinned at `[a, a+4)`. -/
def Pin4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) : Prop :=
  mem[a]? = some (w.extractLsb' 0 8) ∧
  mem[a + 1]? = some (w.extractLsb' 8 8) ∧
  mem[a + 2]? = some (w.extractLsb' 16 8) ∧
  mem[a + 3]? = some (w.extractLsb' 24 8)

theorem Pin8_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) :
    Pin8 (writeMap8 mem a (sdData_val v)) a v :=
  ⟨getElem_writeMap8_0 _ _ _, getElem_writeMap8_1 _ _ _, getElem_writeMap8_2 _ _ _,
   getElem_writeMap8_3 _ _ _, getElem_writeMap8_4 _ _ _, getElem_writeMap8_5 _ _ _,
   getElem_writeMap8_6 _ _ _, getElem_writeMap8_7 _ _ _⟩

theorem Pin4_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) :
    Pin4 (writeMap4 mem a w) a w :=
  ⟨getElem_writeMap4_0 _ _ _, getElem_writeMap4_1 _ _ _,
   getElem_writeMap4_2 _ _ _, getElem_writeMap4_3 _ _ _⟩

theorem Pin8_frame {mem mem' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {v : BitVec 64}
    (hf : ∀ k, a ≤ k → k < a + 8 → mem'[k]? = mem[k]?) (h : Pin8 mem a v) : Pin8 mem' a v :=
  ⟨(hf a (by omega) (by omega)).trans h.1,
   (hf (a+1) (by omega) (by omega)).trans h.2.1,
   (hf (a+2) (by omega) (by omega)).trans h.2.2.1,
   (hf (a+3) (by omega) (by omega)).trans h.2.2.2.1,
   (hf (a+4) (by omega) (by omega)).trans h.2.2.2.2.1,
   (hf (a+5) (by omega) (by omega)).trans h.2.2.2.2.2.1,
   (hf (a+6) (by omega) (by omega)).trans h.2.2.2.2.2.2.1,
   (hf (a+7) (by omega) (by omega)).trans h.2.2.2.2.2.2.2⟩

theorem Pin4_frame {mem mem' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {w : BitVec 32}
    (hf : ∀ k, a ≤ k → k < a + 4 → mem'[k]? = mem[k]?) (h : Pin4 mem a w) : Pin4 mem' a w :=
  ⟨(hf a (by omega) (by omega)).trans h.1,
   (hf (a+1) (by omega) (by omega)).trans h.2.1,
   (hf (a+2) (by omega) (by omega)).trans h.2.2.1,
   (hf (a+3) (by omega) (by omega)).trans h.2.2.2⟩

/-! ## The three-slot stack image -/

/-- Memory after the three prologue spills: `s1` (`v9`) at `vsp-24`, `s0` (`v8`) at
`vsp-16`, `ra` (`r`) at `vsp-8`, over the entry memory `m0`. -/
def spStackMem (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  writeMap8 (writeMap8 (writeMap8 m0 (vsp.toNat - 24) (sdData_val v9))
    (vsp.toNat - 16) (sdData_val v8)) (vsp.toNat - 8) (sdData_val r)

theorem spStackMem_frame (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 : BitVec 64)
    (hsp : 64 ≤ vsp.toNat) (a : Nat) (ha : a < vsp.toNat - 24 ∨ vsp.toNat ≤ a) :
    (spStackMem m0 vsp r v8 v9)[a]? = m0[a]? := by
  unfold spStackMem
  rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
    getElem_writeMap8_disjoint _ _ _ _ (by omega),
    getElem_writeMap8_disjoint _ _ _ _ (by omega)]

theorem spStackMem_ra (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 : BitVec 64) :
    Pin8 (spStackMem m0 vsp r v8 v9) (vsp.toNat - 8) r :=
  Pin8_writeMap8 _ _ _

theorem spStackMem_s0 (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 : BitVec 64)
    (hsp : 64 ≤ vsp.toNat) :
    Pin8 (spStackMem m0 vsp r v8 v9) (vsp.toNat - 16) v8 := by
  unfold spStackMem
  exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
    (Pin8_writeMap8 _ _ _)

theorem spStackMem_s1 (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 : BitVec 64)
    (hsp : 64 ≤ vsp.toNat) :
    Pin8 (spStackMem m0 vsp r v8 v9) (vsp.toNat - 24) v9 := by
  unfold spStackMem
  exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
    (Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (Pin8_writeMap8 _ _ _))

theorem spStackMem_ssloaded (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 : BitVec 64)
    (hsp : 0x8001ad50 ≤ vsp.toNat) (h : Vsa.Sim.Code.__ssputs_rLoaded m0) :
    Vsa.Sim.Code.__ssputs_rLoaded (spStackMem m0 vsp r v8 v9) := by
  unfold spStackMem
  exact ssputs_writeMap8_ss _ _ _ (by omega) (ssputs_writeMap8_ss _ _ _ (by omega)
    (ssputs_writeMap8_ss _ _ _ (by omega) h))

theorem spStackMem_mvloaded (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 : BitVec 64)
    (hsp : 0x8001ad50 ≤ vsp.toNat) (h : MemmoveLoaded m0) :
    MemmoveLoaded (spStackMem m0 vsp r v8 v9) := by
  unfold spStackMem
  exact memmove_writeMap8_ss _ _ _ (by omega) (memmove_writeMap8_ss _ _ _ (by omega)
    (memmove_writeMap8_ss _ _ _ (by omega) h))

/-! ## Region / side-condition bundle -/

/-- Region facts for the fast path: the memmove copy regions (`mv`), the sink
struct `[p, p+16)`, the 64-byte stack frame under `vsp`, and pairwise
disjointness of sink / stack / copy windows. -/
structure SpRegions (p d s vsp : BitVec 64) (n : Nat) : Prop where
  mv : MvRegions d s n
  p_lo : 0x80000000 ≤ p.toNat
  p_hi : p.toNat + 16 ≤ 0x100000000
  p_win : tohostAddr + 16 ≤ p.toNat
  p_align : p.toNat % 8 = 0
  sp_lo : 0x80000000 + 64 ≤ vsp.toNat
  sp_hi : vsp.toNat ≤ 0x100000000
  sp_win : tohostAddr + 16 + 64 ≤ vsp.toNat
  sp_align : vsp.toNat % 8 = 0
  sink_dst : p.toNat + 16 ≤ d.toNat ∨ d.toNat + n ≤ p.toNat
  sink_stack : p.toNat + 16 ≤ vsp.toNat - 64 ∨ vsp.toNat ≤ p.toNat
  stack_dst : vsp.toNat ≤ d.toNat ∨ d.toNat + n ≤ vsp.toNat - 64
  stack_src : vsp.toNat ≤ s.toNat ∨ s.toNat + n ≤ vsp.toNat - 64

/-! ## Blanket ghost-frame predicate (`NotWrittenSp`) + per-class helpers

The fast path writes GPRs `x1, x2, x8, x9, x10, x11, x12, x14, x15`; `x13` is
written inside `memmove` (its frame only guarantees `NotWrittenMv`), so it is
excluded too. -/
abbrev NotWrittenSp (R : Register) : Prop :=
  (Register.x1 == R) = false ∧ (Register.x2 == R) = false ∧
  (Register.x8 == R) = false ∧ (Register.x9 == R) = false ∧
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  NotWrittenMv R

theorem NotWrittenSp.x1 {R : Register} (h : NotWrittenSp R) : (Register.x1 == R) = false := h.1
theorem NotWrittenSp.x2 {R : Register} (h : NotWrittenSp R) : (Register.x2 == R) = false := h.2.1
theorem NotWrittenSp.x8 {R : Register} (h : NotWrittenSp R) : (Register.x8 == R) = false := h.2.2.1
theorem NotWrittenSp.x9 {R : Register} (h : NotWrittenSp R) : (Register.x9 == R) = false := h.2.2.2.1
theorem NotWrittenSp.x10 {R : Register} (h : NotWrittenSp R) : (Register.x10 == R) = false := h.2.2.2.2.1
theorem NotWrittenSp.x11 {R : Register} (h : NotWrittenSp R) : (Register.x11 == R) = false := h.2.2.2.2.2.1
theorem NotWrittenSp.x12 {R : Register} (h : NotWrittenSp R) : (Register.x12 == R) = false := h.2.2.2.2.2.2.1
theorem NotWrittenSp.x13 {R : Register} (h : NotWrittenSp R) : (Register.x13 == R) = false := h.2.2.2.2.2.2.2.1
theorem NotWrittenSp.x14 {R : Register} (h : NotWrittenSp R) : (Register.x14 == R) = false := h.2.2.2.2.2.2.2.2.1
theorem NotWrittenSp.x15 {R : Register} (h : NotWrittenSp R) : (Register.x15 == R) = false := h.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenSp.mv {R : Register} (h : NotWrittenSp R) : NotWrittenMv R := h.2.2.2.2.2.2.2.2.2.2

/-- `jal` register frame outside `{rd} ∪ noise` (mirror of `frame_alu_mv`). -/
theorem frame_jal_sp {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd : Register} {link : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd link)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenMv R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jal σ pc vm imm rd link R hmi hpc hrd hnpc hmii

/-! ## Pre / mid / post condition -/

/-- Entry configuration at `0x8001438c`: sink ptr `p` in `a1`, source `s` in `a2`,
length `ofNat n` in `a3`, return address `r`, stack pointer `vsp`, callee-saved
entry values `v8`/`v9`, cursor `d` and capacity `cap32` pinned in the sink,
source bytes `bs` pinned at `[s, s+n)`, `mem = m0`. -/
structure PreSp (g : (R : Register) → Option (RegisterType R))
    (r p d s vsp v8 v9 : BitVec 64) (n : Nat) (cap32 : BitVec 32)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : Vsa.Sim.Code.__ssputs_rLoaded c.σ.mem
  mvloaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x8001438c#64 : BitVec 64)
  a0 : ∃ v, c.σ.regs.get? Register.x10 = some v
  a1 : c.σ.regs.get? Register.x11 = some p
  a2 : c.σ.regs.get? Register.x12 = some s
  a3 : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  sp : c.σ.regs.get? Register.x2 = some vsp
  s0 : c.σ.regs.get? Register.x8 = some v8
  s1 : c.σ.regs.get? Register.x9 = some v9
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : SpRegions p d s vsp n
  cursor : Pin8 m0 p.toNat d
  cap : Pin4 m0 (p.toNat + 12) cap32
  hbs : MvBytes m0 s n bs
  hcap : n < (sign_extend (m := 64) cap32 : BitVec 64).toNat
  memeq : c.σ.mem = m0
  hframe : ∀ R : Register, NotWrittenSp R → c.σ.regs.get? R = g R

/-- Mid-point configuration at `0x800143c4` (back from `memmove`): the copy is
done, the three stack saves and the sink are intact, `sp/s0/s1` hold the
recovered call-time values. -/
structure StSpRet (g : (R : Register) → Option (RegisterType R))
    (r p d s vsp v8 v9 : BitVec 64) (n : Nat) (cap32 : BitVec 32)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : Vsa.Sim.Code.__ssputs_rLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x800143c4#64 : BitVec 64)
  sp : c.σ.regs.get? Register.x2 = some (vsp - 64#64)
  s0 : c.σ.regs.get? Register.x8 = some p
  s1 : c.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 n)
  tick : c.tick < 2
  regions : SpRegions p d s vsp n
  copied : ∀ k, k < n → c.σ.mem[(d.toNat + k)]? = some (bs k)
  cursor : Pin8 c.σ.mem p.toNat d
  cap : Pin4 c.σ.mem (p.toNat + 12) cap32
  save_ra : Pin8 c.σ.mem (vsp.toNat - 8) r
  save_s0 : Pin8 c.σ.mem (vsp.toNat - 16) v8
  save_s1 : Pin8 c.σ.mem (vsp.toNat - 24) v9
  frame : ∀ a, ¬(d.toNat ≤ a ∧ a < d.toNat + n) → ¬(vsp.toNat - 24 ≤ a ∧ a < vsp.toNat) →
    c.σ.mem[a]? = m0[a]?
  hframe : ∀ R : Register, NotWrittenSp R → c.σ.regs.get? R = g R

/-- Postcondition at `PC = r`: success return value, copy done, cursor advanced
to `d + n`, capacity updated to `spNewCap cap32 n`, callee-saved registers and
`sp` restored, all other memory unchanged. -/
def ssputs_fast_post (g : (R : Register) → Option (RegisterType R))
    (r p d _s vsp v8 v9 : BitVec 64) (n : Nat) (cap32 : BitVec 32)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  c.σ.regs.get? Register.x2 = some vsp ∧
  c.σ.regs.get? Register.x8 = some v8 ∧
  c.σ.regs.get? Register.x9 = some v9 ∧
  (∀ k, k < n → c.σ.mem[(d.toNat + k)]? = some (bs k)) ∧
  Pin8 c.σ.mem p.toNat (d + BitVec.ofNat 64 n) ∧
  Pin4 c.σ.mem (p.toNat + 12) (swData (spNewCap cap32 n)) ∧
  (∀ a, ¬(d.toNat ≤ a ∧ a < d.toNat + n) → ¬(p.toNat ≤ a ∧ a < p.toNat + 8) →
    ¬(p.toNat + 12 ≤ a ∧ a < p.toNat + 16) → ¬(vsp.toNat - 24 ≤ a ∧ a < vsp.toNat) →
    c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧
  (∀ R : Register, NotWrittenSp R → c.σ.regs.get? R = g R)

/-! ## Head: entry `0x8001438c` → `memmove` → back at `0x800143c4` -/

theorem tr_ssputs_head (g : (R : Register) → Option (RegisterType R))
    (r p d s vsp v8 v9 : BitVec 64) (n : Nat) (cap32 : BitVec 32)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreSp g r p d s vsp v8 v9 n cap32 m0 bs)
      (StSpRet g r p d s vsp v8 v9 n cap32 m0 bs) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hmvloaded, hpc, ⟨va0, ha0⟩, ha1, ha2, ha3, hra, hsp, hv8, hv9,
    ⟨vmi, hmi⟩, htick, hreg, hcursor, hcap4, hbs, hcaplt, hmemeq, hframe⟩ := hPre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hn1 := hreg.mv.n1
  have hn31 := hreg.mv.n31
  have hplo := hreg.p_lo
  have hphi := hreg.p_hi
  have hpwin := hreg.p_win
  have hpal := hreg.p_align
  have hslo := hreg.sp_lo
  have hshi := hreg.sp_hi
  have hswin := hreg.sp_win
  have hsal := hreg.sp_align
  have hsd := hreg.sink_dst
  have hsstk := hreg.sink_stack
  have hstkd := hreg.stack_dst
  have hstks := hreg.stack_src
  have hdwin := hreg.mv.dst_win
  have hntn : (BitVec.ofNat 64 n : BitVec 64).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hloaded0 : Vsa.Sim.Code.__ssputs_rLoaded m0 := hmemeq ▸ hloaded
  have hmvloaded0 : MemmoveLoaded m0 := hmemeq ▸ hmvloaded
  -- sp / offset arithmetic
  have hspN : (vsp - 64#64).toNat = vsp.toNat - 64 := sp_sub64_toNat vsp (by omega)
  have haddr40 : ((vsp - 64#64) + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat - 24 := by
    rw [off_ed_28 _ (by rw [hspN]; omega), hspN]; omega
  have haddr48 : ((vsp - 64#64) + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat - 16 := by
    rw [off_ed_30 _ (by rw [hspN]; omega), hspN]; omega
  have haddr56 : ((vsp - 64#64) + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat - 8 := by
    rw [off_ed_38 _ (by rw [hspN]; omega), hspN]; omega
  have hoffc : ((p : BitVec 64) + sign_extend (m := 64) (0x00c#12)).toNat = p.toNat + 12 :=
    off_sp_0c p (by omega)
  have hoff0 : ((p : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat = p.toNat :=
    off_ed_00 p
  -- === 1438c: addi sp,sp,-64 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_1438c_sp c.σ c.tick c.steps (0x8001438c#64) vmi vsp
      hgood hpc hmi hsp hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80014390#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8001438c#64) 4 = (0x80014390#64 : BitVec 64) from by decide] at this
  have hsp1 : σ1.regs.get? Register.x2 = some (vsp - 64#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_sub64 vsp] at this
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have ha3_1 := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have hs0_1 := obs_alu_other' hobs1 Register.x8 (by decide) hv8
  have hs1_1 := obs_alu_other' hobs1 Register.x9 (by decide) hv9
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- === 14390: sd s1,40(sp) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_14390_sp σ1 i1 (c.steps + 1) (0x80014390#64) vmi1 (vsp - 64#64) v9
      hG1 hpc1 hmi1 hsp1 hs1_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr40]; omega) (by rw [haddr40]; omega)
      (by rw [haddr40]; omega) (by rw [haddr40]; omega) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80014394#64 : BitVec 64) := by
    have := obs_store_pc hobs2
    rwa [show BitVec.addInt (0x80014390#64) 4 = (0x80014394#64 : BitVec 64) from by decide] at this
  have hm2 : σ2.mem = writeMap8 m0 (vsp.toNat - 24) (sdData_val v9) := by
    rw [hmem2, mem_afterNextPC, hmem1, hmemeq, haddr40]
  have hsp2 := obs_store_other' hobs2 Register.x2 (by decide) hsp1
  have ha1_2 := obs_store_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_store_other' hobs2 Register.x12 (by decide) ha2_1
  have ha3_2 := obs_store_other' hobs2 Register.x13 (by decide) ha3_1
  have hra_2 := obs_store_other' hobs2 Register.x1 (by decide) hra_1
  have hs0_2 := obs_store_other' hobs2 Register.x8 (by decide) hs0_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret hobs2
  have hload2 : Vsa.Sim.Code.__ssputs_rLoaded σ2.mem := by
    rw [hm2]; exact ssputs_writeMap8_ss _ _ _ (by omega) hloaded0
  -- === 14394: lw s1,12(a1) ===
  have hpin3 : Pin4 σ2.mem ((p + sign_extend (m := 64) (0x00c#12)).toNat) cap32 := by
    rw [hm2, hoffc]
    exact Pin4_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega)) hcap4
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_14394_sp σ2 i2 (c.steps + 1 + 1) (0x80014394#64) vmi2 p
      (cap32.extractLsb' 0 8) (cap32.extractLsb' 8 8)
      (cap32.extractLsb' 16 8) (cap32.extractLsb' 24 8)
      hG2 hpc2 hmi2 ha1_2 hload2 rfl
      (by rw [hoffc]; omega) (by rw [hoffc]; omega)
      (Or.inr (by rw [hoffc]; omega)) (by rw [hoffc]; omega)
      hpin3.1 hpin3.2.1 hpin3.2.2.1 hpin3.2.2.2 hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80014398#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80014394#64) 4 = (0x80014398#64 : BitVec 64) from by decide] at this
  have hs1_3 : σ3.regs.get? Register.x9 = some (sign_extend (m := 64) cap32 : BitVec 64) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [lw_cap_reassemble_sp cap32] at this
  have hsp3 := obs_alu_other' hobs3 Register.x2 (by decide) hsp2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
  have ha3_3 := obs_alu_other' hobs3 Register.x13 (by decide) ha3_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hs0_3 := obs_alu_other' hobs3 Register.x8 (by decide) hs0_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  -- === 14398: sd s0,48(sp) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_14398_sp σ3 i3 (c.steps + 1 + 1 + 1) (0x80014398#64) vmi3 (vsp - 64#64) v8
      hG3 hpc3 hmi3 hsp3 hs0_3 (by rw [hmem3]; exact hload2) rfl
      (by rw [haddr48]; omega) (by rw [haddr48]; omega)
      (by rw [haddr48]; omega) (by rw [haddr48]; omega) hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x8001439c#64 : BitVec 64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x80014398#64) 4 = (0x8001439c#64 : BitVec 64) from by decide] at this
  have hm4 : σ4.mem = writeMap8 (writeMap8 m0 (vsp.toNat - 24) (sdData_val v9))
      (vsp.toNat - 16) (sdData_val v8) := by
    rw [hmem4, mem_afterNextPC, hmem3, hm2, haddr48]
  have hsp4 := obs_store_other' hobs4 Register.x2 (by decide) hsp3
  have ha1_4 := obs_store_other' hobs4 Register.x11 (by decide) ha1_3
  have ha2_4 := obs_store_other' hobs4 Register.x12 (by decide) ha2_3
  have ha3_4 := obs_store_other' hobs4 Register.x13 (by decide) ha3_3
  have hra_4 := obs_store_other' hobs4 Register.x1 (by decide) hra_3
  have hs1_4 := obs_store_other' hobs4 Register.x9 (by decide) hs1_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hload4 : Vsa.Sim.Code.__ssputs_rLoaded σ4.mem := by
    rw [hm4]
    exact ssputs_writeMap8_ss _ _ _ (by omega) (ssputs_writeMap8_ss _ _ _ (by omega) hloaded0)
  -- === 1439c: sd ra,56(sp) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_1439c_sp σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8001439c#64) vmi4 (vsp - 64#64) r
      hG4 hpc4 hmi4 hsp4 hra_4 hload4 rfl
      (by rw [haddr56]; omega) (by rw [haddr56]; omega)
      (by rw [haddr56]; omega) (by rw [haddr56]; omega) hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x800143a0#64 : BitVec 64) := by
    have := obs_store_pc hobs5
    rwa [show BitVec.addInt (0x8001439c#64) 4 = (0x800143a0#64 : BitVec 64) from by decide] at this
  have hm5 : σ5.mem = spStackMem m0 vsp r v8 v9 := by
    rw [hmem5, mem_afterNextPC, hm4, haddr56]; rfl
  have hsp5 := obs_store_other' hobs5 Register.x2 (by decide) hsp4
  have ha1_5 := obs_store_other' hobs5 Register.x11 (by decide) ha1_4
  have ha2_5 := obs_store_other' hobs5 Register.x12 (by decide) ha2_4
  have ha3_5 := obs_store_other' hobs5 Register.x13 (by decide) ha3_4
  have hs1_5 := obs_store_other' hobs5 Register.x9 (by decide) hs1_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hloadS : Vsa.Sim.Code.__ssputs_rLoaded (spStackMem m0 vsp r v8 v9) :=
    spStackMem_ssloaded m0 vsp r v8 v9 (by omega) hloaded0
  have hload5 : Vsa.Sim.Code.__ssputs_rLoaded σ5.mem := by rw [hm5]; exact hloadS
  -- === 143a0: mv s0,a1 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_143a0_sp σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x800143a0#64) vmi5 p
      hG5 hpc5 hmi5 ha1_5 hload5 rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x800143a4#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x800143a0#64) 4 = (0x800143a4#64 : BitVec 64) from by decide] at this
  have hs0_6 : σ6.regs.get? Register.x8 = some p := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add p] at this
  have hsp6 := obs_alu_other' hobs6 Register.x2 (by decide) hsp5
  have ha2_6 := obs_alu_other' hobs6 Register.x12 (by decide) ha2_5
  have ha3_6 := obs_alu_other' hobs6 Register.x13 (by decide) ha3_5
  have hs1_6 := obs_alu_other' hobs6 Register.x9 (by decide) hs1_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  -- === 143a4: mv a5,a2 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_143a4_sp σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x800143a4#64) vmi6 s
      hG6 hpc6 hmi6 ha2_6 (by rw [hmem6]; exact hload5) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x800143a8#64 : BitVec 64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800143a4#64) 4 = (0x800143a8#64 : BitVec 64) from by decide] at this
  have ha5_7 : σ7.regs.get? Register.x15 = some s := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add s] at this
  have hsp7 := obs_alu_other' hobs7 Register.x2 (by decide) hsp6
  have ha3_7 := obs_alu_other' hobs7 Register.x13 (by decide) ha3_6
  have hs1_7 := obs_alu_other' hobs7 Register.x9 (by decide) hs1_6
  have hs0_7 := obs_alu_other' hobs7 Register.x8 (by decide) hs0_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  -- === 143a8: bgeu a3,s1 NOT taken (n <u sext32 cap32) ===
  have hguard : zopz0zKzJ_u (BitVec.ofNat 64 n) (sign_extend (m := 64) cap32 : BitVec 64) = false :=
    bgeu_false_of_lt _ _ (by rw [hntn]; exact hcaplt)
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_143a8_sp σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143a8#64) vmi7
      (BitVec.ofNat 64 n) (sign_extend (m := 64) cap32)
      hG7 hpc7 hmi7 ha3_7 hs1_7 (by rw [hmem7, hmem6]; exact hload5) rfl hguard hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x800143ac#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs8
    rwa [show BitVec.addInt (0x800143a8#64) 4 = (0x800143ac#64 : BitVec 64) from by decide] at this
  have hsp8 := obs_bnottaken_other' hobs8 Register.x2 (by decide) hsp7
  have ha3_8 := obs_bnottaken_other' hobs8 Register.x13 (by decide) ha3_7
  have hs0_8 := obs_bnottaken_other' hobs8 Register.x8 (by decide) hs0_7
  have ha5_8 := obs_bnottaken_other' hobs8 Register.x15 (by decide) ha5_7
  obtain ⟨vmi8, hmi8⟩ := obs_bnottaken_minstret hobs8
  -- === 143ac: sext.w a4,a3 ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_143ac_sp σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143ac#64) vmi8
      (BitVec.ofNat 64 n)
      hG8 hpc8 hmi8 ha3_8 (by rw [hmem8, hmem7, hmem6]; exact hload5) rfl hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x800143b0#64 : BitVec 64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x800143ac#64) 4 = (0x800143b0#64 : BitVec 64) from by decide] at this
  have ha4_9 : σ9.regs.get? Register.x14 = some (BitVec.ofNat 64 n) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sextw_ofNat_sp n (by omega)] at this
  have hsp9 := obs_alu_other' hobs9 Register.x2 (by decide) hsp8
  have hs0_9 := obs_alu_other' hobs9 Register.x8 (by decide) hs0_8
  have ha5_9 := obs_alu_other' hobs9 Register.x15 (by decide) ha5_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hm9 : σ9.mem = spStackMem m0 vsp r v8 v9 := by
    rw [hmem9, hmem8, hmem7, hmem6, hm5]
  -- === 143b0: ld a0,0(s0) ===
  have hpin10 : Pin8 σ9.mem ((p + sign_extend (m := 64) (0x000#12)).toNat) d := by
    rw [hm9, hoff0]
    exact Pin8_frame
      (fun k hk1 hk2 => spStackMem_frame m0 vsp r v8 v9 (by omega) k (by omega)) hcursor
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_143b0_sp σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143b0#64) vmi9 p
      ((sdData_val d).extractLsb' 0 8) ((sdData_val d).extractLsb' 8 8)
      ((sdData_val d).extractLsb' 16 8) ((sdData_val d).extractLsb' 24 8)
      ((sdData_val d).extractLsb' 32 8) ((sdData_val d).extractLsb' 40 8)
      ((sdData_val d).extractLsb' 48 8) ((sdData_val d).extractLsb' 56 8)
      hG9 hpc9 hmi9 hs0_9 (by rw [hm9]; exact hloadS) rfl
      (by rw [hoff0]; omega) (by rw [hoff0]; omega) (Or.inr (by rw [hoff0]; omega))
      (by rw [hoff0]; omega)
      hpin10.1 hpin10.2.1 hpin10.2.2.1 hpin10.2.2.2.1 hpin10.2.2.2.2.1 hpin10.2.2.2.2.2.1
      hpin10.2.2.2.2.2.2.1 hpin10.2.2.2.2.2.2.2 hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x800143b4#64 : BitVec 64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x800143b0#64) 4 = (0x800143b4#64 : BitVec 64) from by decide] at this
  have ha0_10 : σ10.regs.get? Register.x10 = some d := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble d _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  have hsp10 := obs_alu_other' hobs10 Register.x2 (by decide) hsp9
  have hs0_10 := obs_alu_other' hobs10 Register.x8 (by decide) hs0_9
  have ha5_10 := obs_alu_other' hobs10 Register.x15 (by decide) ha5_9
  have ha4_10 := obs_alu_other' hobs10 Register.x14 (by decide) ha4_9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  -- === 143b4: mv s1,a4 ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_143b4_sp σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143b4#64)
      vmi10 (BitVec.ofNat 64 n)
      hG10 hpc10 hmi10 ha4_10 (by rw [hmem10, hm9]; exact hloadS) rfl hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x800143b8#64 : BitVec 64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x800143b4#64) 4 = (0x800143b8#64 : BitVec 64) from by decide] at this
  have hs1_11 : σ11.regs.get? Register.x9 = some (BitVec.ofNat 64 n) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add (BitVec.ofNat 64 n)] at this
  have hsp11 := obs_alu_other' hobs11 Register.x2 (by decide) hsp10
  have hs0_11 := obs_alu_other' hobs11 Register.x8 (by decide) hs0_10
  have ha5_11 := obs_alu_other' hobs11 Register.x15 (by decide) ha5_10
  have ha0_11 := obs_alu_other' hobs11 Register.x10 (by decide) ha0_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  -- === 143b8: mv a1,a5 ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_143b8_sp σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143b8#64)
      vmi11 s
      hG11 hpc11 hmi11 ha5_11 (by rw [hmem11, hmem10, hm9]; exact hloadS) rfl hi11
  have hpc12 : σ12.regs.get? Register.PC = some (0x800143bc#64 : BitVec 64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x800143b8#64) 4 = (0x800143bc#64 : BitVec 64) from by decide] at this
  have ha1_12 : σ12.regs.get? Register.x11 = some s := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add s] at this
  have hsp12 := obs_alu_other' hobs12 Register.x2 (by decide) hsp11
  have hs0_12 := obs_alu_other' hobs12 Register.x8 (by decide) hs0_11
  have hs1_12 := obs_alu_other' hobs12 Register.x9 (by decide) hs1_11
  have ha0_12 := obs_alu_other' hobs12 Register.x10 (by decide) ha0_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  -- === 143bc: mv a2,s1 ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_143bc_sp σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (0x800143bc#64) vmi12 (BitVec.ofNat 64 n)
      hG12 hpc12 hmi12 hs1_12 (by rw [hmem12, hmem11, hmem10, hm9]; exact hloadS) rfl hi12
  have hpc13 : σ13.regs.get? Register.PC = some (0x800143c0#64 : BitVec 64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x800143bc#64) 4 = (0x800143c0#64 : BitVec 64) from by decide] at this
  have ha2_13 : σ13.regs.get? Register.x12 = some (BitVec.ofNat 64 n) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add (BitVec.ofNat 64 n)] at this
  have hsp13 := obs_alu_other' hobs13 Register.x2 (by decide) hsp12
  have hs0_13 := obs_alu_other' hobs13 Register.x8 (by decide) hs0_12
  have hs1_13 := obs_alu_other' hobs13 Register.x9 (by decide) hs1_12
  have ha0_13 := obs_alu_other' hobs13 Register.x10 (by decide) ha0_12
  have ha1_13 := obs_alu_other' hobs13 Register.x11 (by decide) ha1_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  -- === 143c0: jal ra,memmove ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_143c0_sp σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (0x800143c0#64) vmi13
      hG13 hpc13 hmi13 (by rw [hmem13, hmem12, hmem11, hmem10, hm9]; exact hloadS) rfl hi13
  have hpc14 : σ14.regs.get? Register.PC = some (0x800069c4#64 : BitVec 64) := by
    have := obs_jal_pc hobs14
    rwa [show (0x800143c0#64 : BitVec 64) + sign_extend (m := 64) (0x1f2604#21)
        = (0x800069c4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hra14 : σ14.regs.get? Register.x1 = some (0x800143c4#64 : BitVec 64) := by
    have := obs_jal_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800143c0#64) 4 = (0x800143c4#64 : BitVec 64) from by decide] at this
  have hsp14 := obs_jal_other' hobs14 Register.x2 (by decide) hsp13
  have hs0_14 := obs_jal_other' hobs14 Register.x8 (by decide) hs0_13
  have hs1_14 := obs_jal_other' hobs14 Register.x9 (by decide) hs1_13
  have ha0_14 := obs_jal_other' hobs14 Register.x10 (by decide) ha0_13
  have ha1_14 := obs_jal_other' hobs14 Register.x11 (by decide) ha1_13
  have ha2_14 := obs_jal_other' hobs14 Register.x12 (by decide) ha2_13
  have hm14 : σ14.mem = spStackMem m0 vsp r v8 v9 := by
    rw [hmem14, hmem13, hmem12, hmem11, hmem10, hm9]
  -- === memmove_fwd_spec at the call ===
  obtain ⟨c', hsteps_mv, hpost⟩ :=
    memmove_fwd_spec (fun R => σ14.regs.get? R) (0x800143c4#64) d s n
      (spStackMem m0 vsp r v8 v9) bs (by decide)
      ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG14, by rw [hm14]; exact spStackMem_mvloaded m0 vsp r v8 v9 (by omega) hmvloaded0,
       hpc14, ha0_14, ha1_14, ha2_14, hra14, obs_jal_minstret hobs14, hi14, hreg.mv,
       fun k hk => by
         rw [spStackMem_frame m0 vsp r v8 v9 (by omega) _ (by omega)]
         exact hbs k hk,
       hm14, fun R _ => rfl⟩
  obtain ⟨hG', hpc', hx10', hx1', hcopied, hmframe, htick', hregframe⟩ := hpost
  -- recovered registers
  have hsp' : c'.σ.regs.get? Register.x2 = some (vsp - 64#64) :=
    (hregframe Register.x2 (by decide)).trans hsp14
  have hs0' : c'.σ.regs.get? Register.x8 = some p :=
    (hregframe Register.x8 (by decide)).trans hs0_14
  have hs1' : c'.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 n) :=
    (hregframe Register.x9 (by decide)).trans hs1_14
  -- memory facts at the return point
  have hframe' : ∀ a, ¬(d.toNat ≤ a ∧ a < d.toNat + n) →
      ¬(vsp.toNat - 24 ≤ a ∧ a < vsp.toNat) → c'.σ.mem[a]? = m0[a]? := fun a hnd hnstk =>
    (hmframe a (by omega)).trans (spStackMem_frame m0 vsp r v8 v9 (by omega) a (by omega))
  have hloaded' : Vsa.Sim.Code.__ssputs_rLoaded c'.σ.mem :=
    ssputs_frame_ss m0 c'.σ.mem (fun a ha => hframe' a (by omega) (by omega)) hloaded0
  have hcursor' : Pin8 c'.σ.mem p.toNat d :=
    Pin8_frame (fun k hk1 hk2 => hframe' k (by omega) (by omega)) hcursor
  have hcap' : Pin4 c'.σ.mem (p.toNat + 12) cap32 :=
    Pin4_frame (fun k hk1 hk2 => hframe' k (by omega) (by omega)) hcap4
  have hsra' : Pin8 c'.σ.mem (vsp.toNat - 8) r :=
    Pin8_frame (fun k hk1 hk2 => hmframe k (by omega)) (spStackMem_ra m0 vsp r v8 v9)
  have hss0' : Pin8 c'.σ.mem (vsp.toNat - 16) v8 :=
    Pin8_frame (fun k hk1 hk2 => hmframe k (by omega)) (spStackMem_s0 m0 vsp r v8 v9 (by omega))
  have hss1' : Pin8 c'.σ.mem (vsp.toNat - 24) v9 :=
    Pin8_frame (fun k hk1 hk2 => hmframe k (by omega)) (spStackMem_s1 m0 vsp r v8 v9 (by omega))
  -- assemble
  refine ⟨c', ?_, hG', hloaded', hpc', hsp', hs0', hs1', htick', hreg, hcopied,
    hcursor', hcap', hsra', hss0', hss1', hframe', ?_⟩
  · exact ((((((((((((((Steps.single hs1).trans (Steps.single hs2)).trans
      (Steps.single hs3)).trans (Steps.single hs4)).trans (Steps.single hs5)).trans
      (Steps.single hs6)).trans (Steps.single hs7)).trans (Steps.single hs8)).trans
      (Steps.single hs9)).trans (Steps.single hs10)).trans (Steps.single hs11)).trans
      (Steps.single hs12)).trans (Steps.single hs13)).trans (Steps.single hs14)).trans
      hsteps_mv
  · intro R hR
    have hmvR := hR.mv
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.x2 hmvR
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_store_mv hobs2 R hmvR
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_mv hobs3 R hR.x9 hmvR
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_mv hobs4 R hmvR
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_store_mv hobs5 R hmvR
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_alu_mv hobs6 R hR.x8 hmvR
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_alu_mv hobs7 R hR.x15 hmvR
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_bnottaken_mv hobs8 R hmvR
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frame_alu_mv hobs9 R hR.x14 hmvR
    have e10 : σ10.regs.get? R = σ9.regs.get? R := frame_alu_mv hobs10 R hR.x10 hmvR
    have e11 : σ11.regs.get? R = σ10.regs.get? R := frame_alu_mv hobs11 R hR.x9 hmvR
    have e12 : σ12.regs.get? R = σ11.regs.get? R := frame_alu_mv hobs12 R hR.x11 hmvR
    have e13 : σ13.regs.get? R = σ12.regs.get? R := frame_alu_mv hobs13 R hR.x12 hmvR
    have e14 : σ14.regs.get? R = σ13.regs.get? R := frame_jal_sp hobs14 R hR.x1 hmvR
    have emv : c'.σ.regs.get? R = σ14.regs.get? R := hregframe R hmvR
    rw [emv, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
    exact hframe R hR

/-! ## Tail: `0x800143c4` → cursor/capacity update → epilogue → `ret` -/

theorem tr_ssputs_tail (g : (R : Register) → Option (RegisterType R))
    (r p d s vsp v8 v9 : BitVec 64) (n : Nat) (cap32 : BitVec 32)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0) :
    Triple (StSpRet g r p d s vsp v8 v9 n cap32 m0 bs)
      (ssputs_fast_post g r p d s vsp v8 v9 n cap32 m0 bs) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, hsp, hx8p, hx9n, htick, hreg, hcopied, hcursor, hcap4,
    hsra, hss0, hss1, hmframe, hframe⟩ := hSt
  obtain ⟨vmi, hmi⟩ := hgood.minstret
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hn1 := hreg.mv.n1
  have hn31 := hreg.mv.n31
  have hplo := hreg.p_lo
  have hphi := hreg.p_hi
  have hpwin := hreg.p_win
  have hpal := hreg.p_align
  have hslo := hreg.sp_lo
  have hshi := hreg.sp_hi
  have hswin := hreg.sp_win
  have hsal := hreg.sp_align
  have hsd := hreg.sink_dst
  have hsstk := hreg.sink_stack
  have hspN : (vsp - 64#64).toNat = vsp.toNat - 64 := sp_sub64_toNat vsp (by omega)
  have haddr40 : ((vsp - 64#64) + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat - 24 := by
    rw [off_ed_28 _ (by rw [hspN]; omega), hspN]; omega
  have haddr48 : ((vsp - 64#64) + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat - 16 := by
    rw [off_ed_30 _ (by rw [hspN]; omega), hspN]; omega
  have haddr56 : ((vsp - 64#64) + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat - 8 := by
    rw [off_ed_38 _ (by rw [hspN]; omega), hspN]; omega
  have hoffc : ((p : BitVec 64) + sign_extend (m := 64) (0x00c#12)).toNat = p.toNat + 12 :=
    off_sp_0c p (by omega)
  have hoff0 : ((p : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat = p.toNat :=
    off_ed_00 p
  -- === 143c4: lw a4,12(s0) ===
  have hpinT1 : Pin4 c.σ.mem ((p + sign_extend (m := 64) (0x00c#12)).toNat) cap32 := by
    rw [hoffc]; exact hcap4
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_143c4_sp c.σ c.tick c.steps (0x800143c4#64) vmi p
      (cap32.extractLsb' 0 8) (cap32.extractLsb' 8 8)
      (cap32.extractLsb' 16 8) (cap32.extractLsb' 24 8)
      hgood hpc hmi hx8p hloaded rfl
      (by rw [hoffc]; omega) (by rw [hoffc]; omega)
      (Or.inr (by rw [hoffc]; omega)) (by rw [hoffc]; omega)
      hpinT1.1 hpinT1.2.1 hpinT1.2.2.1 hpinT1.2.2.2 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x800143c8#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800143c4#64) 4 = (0x800143c8#64 : BitVec 64) from by decide] at this
  have ha4_1 : σ1.regs.get? Register.x14 = some (sign_extend (m := 64) cap32 : BitVec 64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [lw_cap_reassemble_sp cap32] at this
  have hsp1 := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  have hs0_1 := obs_alu_other' hobs1 Register.x8 (by decide) hx8p
  have hs1_1 := obs_alu_other' hobs1 Register.x9 (by decide) hx9n
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- === 143c8: ld a5,0(s0) ===
  have hpinT2 : Pin8 σ1.mem ((p + sign_extend (m := 64) (0x000#12)).toNat) d := by
    rw [hmem1, hoff0]; exact hcursor
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_143c8_sp σ1 i1 (c.steps + 1) (0x800143c8#64) vmi1 p
      ((sdData_val d).extractLsb' 0 8) ((sdData_val d).extractLsb' 8 8)
      ((sdData_val d).extractLsb' 16 8) ((sdData_val d).extractLsb' 24 8)
      ((sdData_val d).extractLsb' 32 8) ((sdData_val d).extractLsb' 40 8)
      ((sdData_val d).extractLsb' 48 8) ((sdData_val d).extractLsb' 56 8)
      hG1 hpc1 hmi1 hs0_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [hoff0]; omega) (by rw [hoff0]; omega) (Or.inr (by rw [hoff0]; omega))
      (by rw [hoff0]; omega)
      hpinT2.1 hpinT2.2.1 hpinT2.2.2.1 hpinT2.2.2.2.1 hpinT2.2.2.2.2.1 hpinT2.2.2.2.2.2.1
      hpinT2.2.2.2.2.2.2.1 hpinT2.2.2.2.2.2.2.2 hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x800143cc#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800143c8#64) 4 = (0x800143cc#64 : BitVec 64) from by decide] at this
  have ha5_2 : σ2.regs.get? Register.x15 = some d := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble d _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  have hsp2 := obs_alu_other' hobs2 Register.x2 (by decide) hsp1
  have hs0_2 := obs_alu_other' hobs2 Register.x8 (by decide) hs0_1
  have hs1_2 := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  -- === 143cc: li a0,0 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_143cc_sp σ2 i2 (c.steps + 1 + 1) (0x800143cc#64) vmi2
      hG2 hpc2 hmi2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x800143d0#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800143cc#64) 4 = (0x800143d0#64 : BitVec 64) from by decide] at this
  have ha0_3 : σ3.regs.get? Register.x10 = some (0#64 : BitVec 64) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add (0#64)] at this
  have hsp3 := obs_alu_other' hobs3 Register.x2 (by decide) hsp2
  have hs0_3 := obs_alu_other' hobs3 Register.x8 (by decide) hs0_2
  have hs1_3 := obs_alu_other' hobs3 Register.x9 (by decide) hs1_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  -- === 143d0: subw a4,a4,s1 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_143d0_sp σ3 i3 (c.steps + 1 + 1 + 1) (0x800143d0#64) vmi3
      (sign_extend (m := 64) cap32) (BitVec.ofNat 64 n)
      hG3 hpc3 hmi3 ha4_3 hs1_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x800143d4#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x800143d0#64) 4 = (0x800143d4#64 : BitVec 64) from by decide] at this
  have ha4_4 : σ4.regs.get? Register.x14 = some (spNewCap cap32 n) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp4 := obs_alu_other' hobs4 Register.x2 (by decide) hsp3
  have hs0_4 := obs_alu_other' hobs4 Register.x8 (by decide) hs0_3
  have hs1_4 := obs_alu_other' hobs4 Register.x9 (by decide) hs1_3
  have ha5_4 := obs_alu_other' hobs4 Register.x15 (by decide) ha5_3
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  -- === 143d4: add a5,a5,s1 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_143d4_sp σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800143d4#64) vmi4
      d (BitVec.ofNat 64 n)
      hG4 hpc4 hmi4 ha5_4 hs1_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x800143d8#64 : BitVec 64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800143d4#64) 4 = (0x800143d8#64 : BitVec 64) from by decide] at this
  have ha5_5 : σ5.regs.get? Register.x15 = some (d + BitVec.ofNat 64 n) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp5 := obs_alu_other' hobs5 Register.x2 (by decide) hsp4
  have hs0_5 := obs_alu_other' hobs5 Register.x8 (by decide) hs0_4
  have ha4_5 := obs_alu_other' hobs5 Register.x14 (by decide) ha4_4
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  -- === 143d8: sw a4,12(s0) ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_143d8_sp σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x800143d8#64) vmi5 p (spNewCap cap32 n)
      hG5 hpc5 hmi5 hs0_5 ha4_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl
      (by rw [hoffc]; omega) (by rw [hoffc]; omega)
      (by rw [hoffc]; omega) (by rw [hoffc]; omega) hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x800143dc#64 : BitVec 64) := by
    have := obs_store_pc hobs6
    rwa [show BitVec.addInt (0x800143d8#64) 4 = (0x800143dc#64 : BitVec 64) from by decide] at this
  have hm6 : σ6.mem = writeMap4 c.σ.mem (p.toNat + 12) (swData (spNewCap cap32 n)) := by
    rw [hmem6, mem_afterNextPC, hmem5, hmem4, hmem3, hmem2, hmem1, hoffc]
  have hsp6 := obs_store_other' hobs6 Register.x2 (by decide) hsp5
  have hs0_6 := obs_store_other' hobs6 Register.x8 (by decide) hs0_5
  have ha5_6 := obs_store_other' hobs6 Register.x15 (by decide) ha5_5
  have ha0_6 := obs_store_other' hobs6 Register.x10 (by decide) ha0_5
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
  have hloadW4 : Vsa.Sim.Code.__ssputs_rLoaded
      (writeMap4 c.σ.mem (p.toNat + 12) (swData (spNewCap cap32 n))) :=
    ssputs_writeMap4_ss _ _ _ (by omega) hloaded
  -- === 143dc: sd a5,0(s0) ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_143dc_sp σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x800143dc#64) vmi6 p
      (d + BitVec.ofNat 64 n)
      hG6 hpc6 hmi6 hs0_6 ha5_6 (by rw [hm6]; exact hloadW4) rfl
      (by rw [hoff0]; omega) (by rw [hoff0]; omega)
      (by rw [hoff0]; omega) (by rw [hoff0]; omega) hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x800143e0#64 : BitVec 64) := by
    have := obs_store_pc hobs7
    rwa [show BitVec.addInt (0x800143dc#64) 4 = (0x800143e0#64 : BitVec 64) from by decide] at this
  have hm7 : σ7.mem = writeMap8 (writeMap4 c.σ.mem (p.toNat + 12) (swData (spNewCap cap32 n)))
      p.toNat (sdData_val (d + BitVec.ofNat 64 n)) := by
    rw [hmem7, mem_afterNextPC, hm6, hoff0]
  have hsp7 := obs_store_other' hobs7 Register.x2 (by decide) hsp6
  have ha0_7 := obs_store_other' hobs7 Register.x10 (by decide) ha0_6
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hload7 : Vsa.Sim.Code.__ssputs_rLoaded σ7.mem := by
    rw [hm7]; exact ssputs_writeMap8_ss _ _ _ (by omega) hloadW4
  -- === 143e0: ld ra,56(sp) ===
  have hpinT8 : Pin8 σ7.mem (((vsp - 64#64) + sign_extend (m := 64) (0x038#12)).toNat) r := by
    rw [hm7, haddr56]
    exact Pin8_frame (fun k hk1 hk2 => by
        rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
          getElem_writeMap4_disjoint _ _ _ _ (by omega)]) hsra
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_143e0_sp σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143e0#64) vmi7 (vsp - 64#64)
      ((sdData_val r).extractLsb' 0 8) ((sdData_val r).extractLsb' 8 8)
      ((sdData_val r).extractLsb' 16 8) ((sdData_val r).extractLsb' 24 8)
      ((sdData_val r).extractLsb' 32 8) ((sdData_val r).extractLsb' 40 8)
      ((sdData_val r).extractLsb' 48 8) ((sdData_val r).extractLsb' 56 8)
      hG7 hpc7 hmi7 hsp7 hload7 rfl
      (by rw [haddr56]; omega) (by rw [haddr56]; omega) (Or.inr (by rw [haddr56]; omega))
      (by rw [haddr56]; omega)
      hpinT8.1 hpinT8.2.1 hpinT8.2.2.1 hpinT8.2.2.2.1 hpinT8.2.2.2.2.1 hpinT8.2.2.2.2.2.1
      hpinT8.2.2.2.2.2.2.1 hpinT8.2.2.2.2.2.2.2 hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x800143e4#64 : BitVec 64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x800143e0#64) 4 = (0x800143e4#64 : BitVec 64) from by decide] at this
  have hra_8 : σ8.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble r _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  have hsp8 := obs_alu_other' hobs8 Register.x2 (by decide) hsp7
  have ha0_8 := obs_alu_other' hobs8 Register.x10 (by decide) ha0_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  -- === 143e4: ld s0,48(sp) ===
  have hpinT9 : Pin8 σ7.mem (((vsp - 64#64) + sign_extend (m := 64) (0x030#12)).toNat) v8 := by
    rw [hm7, haddr48]
    exact Pin8_frame (fun k hk1 hk2 => by
        rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
          getElem_writeMap4_disjoint _ _ _ _ (by omega)]) hss0
  rw [show σ7.mem = σ8.mem from hmem8.symm] at hpinT9
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_143e4_sp σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143e4#64) vmi8
      (vsp - 64#64)
      ((sdData_val v8).extractLsb' 0 8) ((sdData_val v8).extractLsb' 8 8)
      ((sdData_val v8).extractLsb' 16 8) ((sdData_val v8).extractLsb' 24 8)
      ((sdData_val v8).extractLsb' 32 8) ((sdData_val v8).extractLsb' 40 8)
      ((sdData_val v8).extractLsb' 48 8) ((sdData_val v8).extractLsb' 56 8)
      hG8 hpc8 hmi8 hsp8 (by rw [hmem8]; exact hload7) rfl
      (by rw [haddr48]; omega) (by rw [haddr48]; omega) (Or.inr (by rw [haddr48]; omega))
      (by rw [haddr48]; omega)
      hpinT9.1 hpinT9.2.1 hpinT9.2.2.1 hpinT9.2.2.2.1 hpinT9.2.2.2.2.1 hpinT9.2.2.2.2.2.1
      hpinT9.2.2.2.2.2.2.1 hpinT9.2.2.2.2.2.2.2 hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x800143e8#64 : BitVec 64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x800143e4#64) 4 = (0x800143e8#64 : BitVec 64) from by decide] at this
  have hs0_9 : σ9.regs.get? Register.x8 = some v8 := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble v8 _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  have hsp9 := obs_alu_other' hobs9 Register.x2 (by decide) hsp8
  have ha0_9 := obs_alu_other' hobs9 Register.x10 (by decide) ha0_8
  have hra_9 := obs_alu_other' hobs9 Register.x1 (by decide) hra_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  -- === 143e8: ld s1,40(sp) ===
  have hpinT10 : Pin8 σ7.mem (((vsp - 64#64) + sign_extend (m := 64) (0x028#12)).toNat) v9 := by
    rw [hm7, haddr40]
    exact Pin8_frame (fun k hk1 hk2 => by
        rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
          getElem_writeMap4_disjoint _ _ _ _ (by omega)]) hss1
  rw [show σ7.mem = σ9.mem from by rw [hmem9, hmem8]] at hpinT10
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_143e8_sp σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143e8#64) vmi9
      (vsp - 64#64)
      ((sdData_val v9).extractLsb' 0 8) ((sdData_val v9).extractLsb' 8 8)
      ((sdData_val v9).extractLsb' 16 8) ((sdData_val v9).extractLsb' 24 8)
      ((sdData_val v9).extractLsb' 32 8) ((sdData_val v9).extractLsb' 40 8)
      ((sdData_val v9).extractLsb' 48 8) ((sdData_val v9).extractLsb' 56 8)
      hG9 hpc9 hmi9 hsp9 (by rw [hmem9, hmem8]; exact hload7) rfl
      (by rw [haddr40]; omega) (by rw [haddr40]; omega) (Or.inr (by rw [haddr40]; omega))
      (by rw [haddr40]; omega)
      hpinT10.1 hpinT10.2.1 hpinT10.2.2.1 hpinT10.2.2.2.1 hpinT10.2.2.2.2.1 hpinT10.2.2.2.2.2.1
      hpinT10.2.2.2.2.2.2.1 hpinT10.2.2.2.2.2.2.2 hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x800143ec#64 : BitVec 64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x800143e8#64) 4 = (0x800143ec#64 : BitVec 64) from by decide] at this
  have hs1_10 : σ10.regs.get? Register.x9 = some v9 := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble v9 _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  have hsp10 := obs_alu_other' hobs10 Register.x2 (by decide) hsp9
  have ha0_10 := obs_alu_other' hobs10 Register.x10 (by decide) ha0_9
  have hra_10 := obs_alu_other' hobs10 Register.x1 (by decide) hra_9
  have hs0_10 := obs_alu_other' hobs10 Register.x8 (by decide) hs0_9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  -- === 143ec: addi sp,sp,64 ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_143ec_sp σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143ec#64)
      vmi10 (vsp - 64#64)
      hG10 hpc10 hmi10 hsp10 (by rw [hmem10, hmem9, hmem8]; exact hload7) rfl hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x800143f0#64 : BitVec 64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x800143ec#64) 4 = (0x800143f0#64 : BitVec 64) from by decide] at this
  have hsp11 : σ11.regs.get? Register.x2 = some vsp := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_restore64 vsp] at this
  have ha0_11 := obs_alu_other' hobs11 Register.x10 (by decide) ha0_10
  have hra_11 := obs_alu_other' hobs11 Register.x1 (by decide) hra_10
  have hs0_11 := obs_alu_other' hobs11 Register.x8 (by decide) hs0_10
  have hs1_11 := obs_alu_other' hobs11 Register.x9 (by decide) hs1_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  -- === 143f0: ret ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_143f0_sp σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800143f0#64)
      vmi11 r
      hG11 hpc11 hmi11 hra_11 (by rw [hmem11, hmem10, hmem9, hmem8]; exact hload7) rfl
      (by rw [ret_tgt r halign]; exact halign) hi11
  have hpcF : σ12.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs12, ret_tgt r halign]
  have ha0_12 := obs_jr_other' hobs12 Register.x10 (by decide) ha0_11
  have hra_12 := obs_jr_other' hobs12 Register.x1 (by decide) hra_11
  have hsp12 := obs_jr_other' hobs12 Register.x2 (by decide) hsp11
  have hs0_12 := obs_jr_other' hobs12 Register.x8 (by decide) hs0_11
  have hs1_12 := obs_jr_other' hobs12 Register.x9 (by decide) hs1_11
  have hmemF : σ12.mem = σ7.mem := by rw [hmem12, hmem11, hmem10, hmem9, hmem8]
  -- assemble the postcondition
  refine ⟨⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans
      (Steps.single hs7)).trans (Steps.single hs8)).trans (Steps.single hs9)).trans
      (Steps.single hs10)).trans (Steps.single hs11)).trans (Steps.single hs12),
    hG12, hpcF, ha0_12, hra_12, hsp12, hs0_12, hs1_12, ?_, ?_, ?_, ?_, hi12, ?_⟩
  · -- the copied window survives the sink stores
    intro k hk
    rw [hmemF, hm7, getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap4_disjoint _ _ _ _ (by omega)]
    exact hcopied k hk
  · -- the cursor slot holds d + n
    rw [hmemF, hm7]
    exact Pin8_writeMap8 _ _ _
  · -- the capacity slot holds swData (spNewCap cap32 n)
    rw [hmemF, hm7]
    exact Pin4_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (Pin4_writeMap4 _ _ _)
  · -- the memory frame
    intro a hnd hn8 hn4 hnstk
    rw [hmemF, hm7, getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap4_disjoint _ _ _ _ (by omega)]
    exact hmframe a hnd hnstk
  · -- the register frame
    intro R hR
    have hmvR := hR.mv
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.x14 hmvR
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_mv hobs2 R hR.x15 hmvR
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_mv hobs3 R hR.x10 hmvR
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_alu_mv hobs4 R hR.x14 hmvR
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_alu_mv hobs5 R hR.x15 hmvR
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_store_mv hobs6 R hmvR
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_store_mv hobs7 R hmvR
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_alu_mv hobs8 R hR.x1 hmvR
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frame_alu_mv hobs9 R hR.x8 hmvR
    have e10 : σ10.regs.get? R = σ9.regs.get? R := frame_alu_mv hobs10 R hR.x9 hmvR
    have e11 : σ11.regs.get? R = σ10.regs.get? R := frame_alu_mv hobs11 R hR.x2 hmvR
    have e12 : σ12.regs.get? R = σ11.regs.get? R := frame_jr_mv hobs12 R hmvR
    rw [e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
    exact hframe R hR

/-! ## The composed fast-path spec -/

/-- **`__ssputs_r` fast path** (`0x8001438c → ret`), composed with the verified
`memmove` forward byte path: copies the `n` source bytes into the cursor buffer,
advances the cursor by `n`, decrements the capacity word by `n` (32-bit), and
returns `0` with callee-saved state restored. -/
theorem ssputs_fast_spec (g : (R : Register) → Option (RegisterType R))
    (r p d s vsp v8 v9 : BitVec 64) (n : Nat) (cap32 : BitVec 32)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0) :
    Triple (PreSp g r p d s vsp v8 v9 n cap32 m0 bs)
      (ssputs_fast_post g r p d s vsp v8 v9 n cap32 m0 bs) :=
  (tr_ssputs_head g r p d s vsp v8 v9 n cap32 m0 bs).seq
    (tr_ssputs_tail g r p d s vsp v8 v9 n cap32 m0 bs halign)

end Vsa.Sim

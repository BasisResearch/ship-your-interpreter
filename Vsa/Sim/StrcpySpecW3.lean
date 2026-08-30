import Vsa.Sim.StrcpySpecW2
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcpy` aligned word-path byte tail + top-level assembly

Builds on `StrcpySpecW2.lean` (`entry_to_tail : Triple PreWord AtTailW`).  This file
closes the aligned word path:

1. **Byte tail** (`wtail_to_done`): from `WTailCpw p` (`0x80006e24`), the unrolled
   lbu/sb/beqz ladder `0xe24…0xe78` copies bytes `8p, 8p+1, …, len` (offset
   `t = len − 8p ∈ [0,7]`) one at a time, exiting to `ret` at `0xe78` (for
   `t ∈ {0..6}`, the `sb` wrote the NUL) or via the `bnez a4,0xe98` finisher
   (`sb zero,7(a2)`) then `ret` at `0xe9c` (for `t = 7`).  Lands the SAME post as
   the byte-head path (`strcpy_bytehead_post`).

2. **`strcpy_word_spec`**: `entry_to_tail ≫ wtail_to_done`, `CString`-phrased,
   IDENTICAL post-shape to `strcpy_spec`.

3. **`strcpy_full_spec`**: `Triple.cases` over the `0xdcc` alignment test unifying the
   misaligned byte-head path (`strcpy_spec`) and the aligned word path
   (`strcpy_word_spec`).

## Byte tail control flow (from `WTailCpw p`, NUL at offset `t = len − 8p`)

```
e24: lbu a5,0(a1)      ; a5 := byte 8p+0
e28: lbu a4,1(a1)      ; a4 := byte 8p+1
e2c: lbu a3,2(a1)      ; a3 := byte 8p+2
e30: sb  a5,0(a2)      ; store byte 8p+0 at dst+8p+0
e34: beqz a5,0xe78     ; t=0 → ret
e38: sb  a4,1(a2)      ; store byte 8p+1
e3c: beqz a4,0xe78     ; t=1 → ret
e40: lbu a5,3(a1)      ; a5 := byte 8p+3
e44: sb  a3,2(a2)      ; store byte 8p+2
e48: beqz a3,0xe78     ; t=2 → ret
e4c: lbu a4,4(a1)      ; a4 := byte 8p+4
e50: sb  a5,3(a2)      ; store byte 8p+3
e54: beqz a5,0xe78     ; t=3 → ret
e58: lbu a5,5(a1)      ; a5 := byte 8p+5
e5c: sb  a4,4(a2)      ; store byte 8p+4
e60: beqz a4,0xe78     ; t=4 → ret
e64: lbu a4,6(a1)      ; a4 := byte 8p+6
e68: sb  a5,5(a2)      ; store byte 8p+5
e6c: beqz a5,0xe78     ; t=5 → ret
e70: sb  a4,6(a2)      ; store byte 8p+6
e74: bnez a4,0xe98     ; t=6 → ret (fall through); t=7 → finisher
e78: ret
e98: sb  zero,7(a2)    ; store NUL byte 8p+7 (= len) at dst+8p+7
e9c: ret
```

Bytes `8p+off` for `off ∈ {0..6}` are read (into a5/a4/a3, alternating) and stored;
the `beqz`/`bnez` after each store tests whether the JUST-STORED byte was the NUL.
For `t = 7` all seven are nonzero, the `bnez a4` at `0xe74` is taken, and the
finisher writes the NUL at `dst+8p+7 = dst+len`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr (CStr CString Mem)
open Vsa.Sim.Code (StrcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-tail helper facts

Under `WTailCpw`'s `MemInv dst src (len+1) bs (8p) m0 mem` with `8p ≤ len < 8p+8`, the
CURRENT-memory byte at `src+8p+off` for `off ≤ t = len−8p` is `bs (8p+off)`
(`src_intact`).  The loaded value `zero_extend (bs (8p+off))` stored via `stData 1`
is exactly `bs (8p+off)`. -/

/-- The current-memory source byte at `src+8p+off` (`off ≤ len−8p`) is `bs (8p+off)`. -/
theorem tail_src_byte (dst src : BitVec 64) (len : Nat) (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (p off : Nat) (hoff : 8*p + off ≤ len)
    (hinv : MemInv dst src (len + 1) bs (8*p) m0 mem) :
    mem[(src.toNat + (8*p + off))]? = some (bs (8*p + off)) :=
  hinv.src_intact (8*p + off) (by omega) (by omega)

/-- Byte `k = 8p+off` (`k ≤ len`) is `bs k` (nonzero for `k < len`, `0` at `k = len`). -/
theorem tail_bs_val (m0 : Mem) (src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8)
    (hsb : StrBytes m0 src len bs) (k : Nat) (hk : k ≤ len) :
    m0[(src.toNat + k)]? = some (bs k) :=
  strbytes_byte m0 src len bs hsb k hk

/-- `stData 1 (zero_extend b) = b` (`BitVec (8*1)` = `BitVec 8`). -/
theorem stData1_zext (b : BitVec 8) :
    stData 1 (zero_extend (m := 64) (b : BitVec (8*1))) = (b : BitVec (8*1)) :=
  stData_zext b

/-- `zext b = 0` (as `== 0#64`) iff `b = 0`.  Used for the tail `beqz`/`bnez` tests. -/
theorem zext_eq_zero_iff (b : BitVec 8) :
    ((zero_extend (m := 64) (b : BitVec (8*1))) == (0#64)) = (b == 0#8) := by
  rcases Decidable.em (b = 0#8) with h | h
  · subst h
    rw [show ((0#8 : BitVec 8) == 0#8) = true from by decide]
    rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]; decide
  · rw [show (b == 0#8) = false from by rw [beq_eq_false_iff_ne]; exact h]
    rw [beq_eq_false_iff_ne, ne_eq]
    have := zext_ne_zero_iff b
    rw [show (b != 0#8) = true from by rw [bne_iff_ne]; exact h] at this
    rw [bne_iff_ne] at this; exact this

/-- `(base + ofNat (8p)) + sext (0x00off#12)` normalizes to `base.toNat + (8p+off)`
when `base` is 8-aligned with no wrap.  `hsx : (sext off#12).toNat = off` is supplied
per-offset by `decide`. -/
theorem tail_store_addr (base : BitVec 64) (p off : Nat) (imm : BitVec 12)
    (hsx : (sign_extend (m := 64) imm : BitVec 64).toNat = off)
    (hnw : base.toNat + 8*p + off < 2^64) :
    ((base + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat
      = base.toNat + (8*p + off) := by
  have hbase : (base + BitVec.ofNat 64 (8*p)).toNat = base.toNat + 8*p :=
    ptrCpw_toNat base p (by omega)
  rw [BitVec.toNat_add, hbase, hsx, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The word-path byte-tail postcondition

Same observable shape as `StrcpySpec.strcpy_bytehead_post` (PC = r, x10 = dst, x1 = r,
the `len` chars + NUL copied into `[dst,dst+len]`, outside unchanged, GoodState,
tick < 2) but with the aligned-path blanket frame `NotWrittenCpw` (the byte tail
writes `x13`/`x14`/`x15`, unlike the byte-head path). -/
def strcpy_word_bytepost (g : (R : Register) → Option (RegisterType R)) (r dst _src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∀ k, k ≤ len → c.σ.mem[(dst.toNat + k)]? = some (bs k)) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + len < a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R)

/-- The final `ret` from the byte tail: PC → r, dst returned, memory carries the
completed `MemInv … (len+1)` (chars + NUL).  `r` 4-aligned. -/
theorem tail_ret (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 mem : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0) (retpc : BitVec 64) (hretpc : retpc = 0x80006e78#64 ∨ retpc = 0x80006e9c#64) :
    Triple (fun c => GoodState c.σ ∧ StrcpyLoaded c.σ.mem ∧
        c.σ.regs.get? Register.PC = some retpc ∧
        c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        MemInv dst src (len + 1) bs (len + 1) m0 c.σ.mem ∧
        (∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R))
      (strcpy_word_bytepost g r dst src len m0 bs) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hpc, ha0, hra, ⟨vmi, hmi⟩, htick, hinv, hframe⟩
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  rcases hretpc with hr | hr
  · subst hr
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006e78 c.σ c.tick c.steps (0x80006e78#64) vmi r hgood hpc hmi hra hloaded rfl htgt htick
    have hpc' : σ'.regs.get? Register.PC = some r := by
      rw [obs_jr_pc hobs, ret_tgt r halign]
    have ha0' := obs_jr_other' hobs Register.x10 (by decide) ha0
    have hra' := obs_jr_other' hobs Register.x1 (by decide) hra
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG', hpc', ha0', hra', ?_, ?_, hi',
      fun R hR => (frame_jr_cpw hobs R hR).trans (hframe R hR)⟩
    · intro k hk; rw [hmem']; exact hinv.copied k (by omega)
    · intro a ha; rw [hmem']; exact hinv.outside a (by omega)
  · subst hr
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006e9c c.σ c.tick c.steps (0x80006e9c#64) vmi r hgood hpc hmi hra hloaded rfl htgt htick
    have hpc' : σ'.regs.get? Register.PC = some r := by
      rw [obs_jr_pc hobs, ret_tgt r halign]
    have ha0' := obs_jr_other' hobs Register.x10 (by decide) ha0
    have hra' := obs_jr_other' hobs Register.x1 (by decide) hra
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG', hpc', ha0', hra', ?_, ?_, hi',
      fun R hR => (frame_jr_cpw hobs R hR).trans (hframe R hR)⟩
    · intro k hk; rw [hmem']; exact hinv.copied k (by omega)
    · intro a ha; rw [hmem']; exact hinv.outside a (by omega)

/-! ## Byte-tail source-word mapping precondition

The unrolled tail reads bytes of the final aligned word `[src+8p, src+8p+8)` with
`lbu` (a NON-total, byte-present load), including up to 6 bytes PAST the NUL (`safe`
by 8-alignment: the whole word was already read by the loop's total `ld`).  At the
model level we require those bytes be MAPPED in `m0`. -/
def SrcWordMapped (m0 : Std.ExtHashMap Nat (BitVec 8)) (src : BitVec 64) (p : Nat) : Prop :=
  ∀ k, k < 8 → ∃ b, m0[(src.toNat + (8*p + k))]? = some b

/-- Current-memory byte at `src+8p+k` (`k < 8`) equals the `m0` byte (source disjoint
from `[dst,dst+len]`), and is mapped. -/
theorem tail_cur_byte (dst src : BitVec 64) (len i : Nat) (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (p k : Nat) (hk : k < 8)
    (hreg : CpwRegions dst src len) (hplo : 8*p ≤ len)
    (hinv : MemInv dst src (len + 1) bs i m0 mem)
    (b : BitVec 8) (hb : m0[(src.toNat + (8*p + k))]? = some b) :
    mem[(src.toNat + (8*p + k))]? = some b := by
  have hout : mem[(src.toNat + (8*p + k))]? = m0[(src.toNat + (8*p + k))]? := by
    apply hinv.outside
    rcases hreg.disjoint with hd | hd
    · right; omega
    · left; omega
  rw [hout]; exact hb

/-! ## Per-offset sext facts (`(sext 0x00off#12).toNat = off`, `off ∈ {0..7}`) -/
theorem sext_off0 : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by decide
theorem sext_off1 : (sign_extend (m := 64) (0x001#12) : BitVec 64).toNat = 1 := by decide
theorem sext_off2 : (sign_extend (m := 64) (0x002#12) : BitVec 64).toNat = 2 := by decide
theorem sext_off3 : (sign_extend (m := 64) (0x003#12) : BitVec 64).toNat = 3 := by decide
theorem sext_off4 : (sign_extend (m := 64) (0x004#12) : BitVec 64).toNat = 4 := by decide
theorem sext_off5 : (sign_extend (m := 64) (0x005#12) : BitVec 64).toNat = 5 := by decide
theorem sext_off6 : (sign_extend (m := 64) (0x006#12) : BitVec 64).toNat = 6 := by decide
theorem sext_off7 : (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 := by decide

/-- `lbu` bounds at `src+8p+off` (`off < 8`, `8p ≤ len`): RAM, HTIF-disjoint, and
`(src+ofNat 8p + sext 0x00off).toNat = src.toNat+8p+off`. -/
theorem wtail_lbu_bounds (dst src : BitVec 64) (len p off : Nat) (imm : BitVec 12)
    (hreg : CpwRegions dst src len) (hplo : 8*p ≤ len) (hoff : off < 8)
    (hsx : (sign_extend (m := 64) imm : BitVec 64).toNat = off) :
    ((src + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat = src.toNat + (8*p + off) ∧
    0x80000000 ≤ ((src + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat ∧
    ((src + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat + 1 ≤ 0x100000000 ∧
    (((src + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat + 1 ≤ tohostAddr ∨
       tohostAddr + 8 ≤ ((src + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat) := by
  have haddr := tail_store_addr src p off imm hsx (by have := hreg.src_nowrap; omega)
  have hlo := hreg.src_lo; have hhi := hreg.src_hi; have hwin := hreg.src_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨haddr, by rw [haddr]; omega, by rw [haddr]; omega, Or.inr (by rw [haddr]; omega)⟩

/-- `sb` bounds at `dst+8p+off` (`off < 8`, `8p ≤ len`): RAM, above HTIF window, and
`(dst+ofNat 8p + sext 0x00off).toNat = dst.toNat+8p+off`. -/
theorem tail_sb_bounds (dst src : BitVec 64) (len p off : Nat) (imm : BitVec 12)
    (hreg : CpwRegions dst src len) (hplo : 8*p ≤ len) (hoff : off < 8)
    (hsx : (sign_extend (m := 64) imm : BitVec 64).toNat = off) :
    ((dst + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat = dst.toNat + (8*p + off) ∧
    0x80000000 ≤ ((dst + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat ∧
    ((dst + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat + 1 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ ((dst + BitVec.ofNat 64 (8*p)) + sign_extend (m := 64) imm).toNat := by
  have haddr := tail_store_addr dst p off imm hsx (by have := hreg.dst_nowrap; omega)
  have hlo := hreg.dst_lo; have hhi := hreg.dst_hi; have hwin := hreg.dst_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨haddr, by rw [haddr]; omega, by rw [haddr]; omega, by rw [haddr]; omega⟩

/-- The `sb` at tail offset `off` (`8p+off ≤ len`) storing `zext (bs (8p+off))` at
`dst+8p+off` extends `MemInv … (8p+off) → MemInv … (8p+off+1)`.  The site's post map
`σ.mem.insert addr (stData 1 (zext (bs …)))` is exactly the `meminv_store` insert. -/
theorem tail_meminv_store (dst src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8) (p off : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8)) (hreg : CpwRegions dst src len)
    (hle : 8*p + off ≤ len) (haddr : addr = dst.toNat + (8*p + off))
    (hinv : MemInv dst src (len + 1) bs (8*p + off) m0 mem) :
    MemInv dst src (len + 1) bs (8*p + off + 1) m0
      (mem.insert addr (stData 1 (zero_extend (m := 64) ((bs (8*p + off)) : BitVec (8*1))))) := by
  rw [haddr, stData_zext]
  exact meminv_store dst src (len + 1) bs (8*p + off) m0 mem (cpw_regions dst src len hreg)
    (by omega) hinv

/-! ## The byte tail: `WTailCpw p → strcpy_word_bytepost`

The unrolled `lbu`/`sb`/`beqz` ladder `0xe24…0xe78` (+ `0xe98` finisher), cased on the
NUL offset `t = len − 8p ∈ [0,7]`.  Each `sb` at offset `off ≤ t` extends the copied
prefix `MemInv … (8p+off) → MemInv … (8p+off+1)`; the `beqz`/`bnez` after storing
offset `off` exits exactly when `off = t` (that byte is the NUL).  For `t ∈ {0..6}` the
exit `ret`s at `0xe78`; for `t = 7` the `bnez a4` at `0xe74` jumps to the `0xe98`
finisher (`sb zero,7(a2)`), then `ret`s at `0xe9c`. -/
theorem wtail_to_done (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (p : Nat)
    (halign : r.toNat % 4 = 0) (hmap : SrcWordMapped m0 src p) :
    Triple (WTailCpw g r dst src len m0 bs p) (strcpy_word_bytepost g r dst src len m0 bs) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha4, hra, ⟨vmi0, hmi0⟩, htick,
    hreg, hstrb, hplo, hphi, hinv0, hframe⟩ := hSt
  have hbyte : ∀ off, off < 8 → ∃ b, m0[(src.toNat + (8*p + off))]? = some b := hmap
  -- STEP e24: lbu a5,0(a1) → a5 = zext (byte 8p+0)
  obtain ⟨b0, hb0m⟩ := hbyte 0 (by omega)
  have hb0cur : c.σ.mem[(src.toNat + (8*p + 0))]? = some b0 :=
    tail_cur_byte dst src len _ m0 c.σ.mem bs p 0 (by omega) hreg hplo hinv0 b0 hb0m
  obtain ⟨lb0, lhlo0, lhhi0, lhtif0⟩ :=
    wtail_lbu_bounds dst src len p 0 (0x000#12) hreg hplo (by omega) sext_off0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006e24 c.σ c.tick c.steps (0x80006e24#64) vmi0 (src + BitVec.ofNat 64 (8*p)) b0
      hgood hpc hmi0 ha1 hloaded rfl lhlo0 lhhi0 lhtif0
      (by rw [lb0]; simpa using hb0cur) htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006e28#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006e24#64) 4 = (0x80006e28#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15 = some (zero_extend (m := 64) (b0 : BitVec (8*1))) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hmem1eq : σ1.mem = c.σ.mem := hmem1
  have hframe1 : ∀ R, NotWrittenCpw R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_cpw hobs1 R hR.x15 hR).trans (hframe R hR)
  -- byte value at offset off ≤ t is bs (8p+off); the NUL is at off = t
  have hval : ∀ off (b : BitVec 8), 8*p + off ≤ len →
      m0[(src.toNat + (8*p + off))]? = some b → b = bs (8*p + off) := by
    intro off b hle hb
    have := strbytes_byte m0 src len bs hstrb (8*p + off) hle
    rw [this] at hb; exact (Option.some.inj hb).symm
  have hbnul : ∀ off (b : BitVec 8), 8*p + off = len →
      m0[(src.toNat + (8*p + off))]? = some b → b = 0 := by
    intro off b heq hb
    have h1 := hval off b (by omega) hb
    rw [h1, show 8*p + off = len from heq, hstrb.bs_nul]
  have hbne : ∀ off (b : BitVec 8), 8*p + off < len →
      m0[(src.toNat + (8*p + off))]? = some b → b ≠ 0 := by
    intro off b hlt hb
    have h1 := hval off b (by omega) hb
    rw [h1]; exact (hstrb.chars (8*p + off) hlt).2
  -- STEP e28: lbu a4,1(a1) → a4 = zext (byte 8p+1)
  obtain ⟨b1, hb1m⟩ := hbyte 1 (by omega)
  have hb1cur : σ1.mem[(src.toNat + (8*p + 1))]? = some b1 := by
    rw [hmem1eq]
    exact tail_cur_byte dst src len _ m0 c.σ.mem bs p 1 (by omega) hreg hplo hinv0 b1 hb1m
  obtain ⟨lb1, lhlo1, lhhi1, lhtif1⟩ :=
    wtail_lbu_bounds dst src len p 1 (0x001#12) hreg hplo (by omega) sext_off1
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006e28 σ1 i1 (c.steps + 1) (0x80006e28#64) vmi1 (src + BitVec.ofNat 64 (8*p)) b1
      hG1 hpc1 hmi1 ha1_1 (by rw [hmem1eq]; exact hloaded) rfl lhlo1 lhhi1 lhtif1
      (by rw [lb1]; simpa using hb1cur) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006e2c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006e28#64) 4 = (0x80006e2c#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha5_1
  have ha4_2 : σ2.regs.get? Register.x14 = some (zero_extend (m := 64) (b1 : BitVec (8*1))) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1eq]
  have hframe2 : ∀ R, NotWrittenCpw R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_cpw hobs2 R hR.x14 hR).trans (hframe1 R hR)
  -- STEP e2c: lbu a3,2(a1) → a3 = zext (byte 8p+2)
  obtain ⟨b2, hb2m⟩ := hbyte 2 (by omega)
  have hb2cur : σ2.mem[(src.toNat + (8*p + 2))]? = some b2 := by
    rw [hmem2eq]
    exact tail_cur_byte dst src len _ m0 c.σ.mem bs p 2 (by omega) hreg hplo hinv0 b2 hb2m
  obtain ⟨lb2, lhlo2, lhhi2, lhtif2⟩ :=
    wtail_lbu_bounds dst src len p 2 (0x002#12) hreg hplo (by omega) sext_off2
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006e2c σ2 i2 (c.steps + 1 + 1) (0x80006e2c#64) vmi2 (src + BitVec.ofNat 64 (8*p)) b2
      hG2 hpc2 hmi2 ha1_2 (by rw [hmem2eq]; exact hloaded) rfl lhlo2 lhhi2 lhtif2
      (by rw [lb2]; simpa using hb2cur) hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006e30#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006e2c#64) 4 = (0x80006e30#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha3_3 : σ3.regs.get? Register.x13 = some (zero_extend (m := 64) (b2 : BitVec (8*1))) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2eq]
  have hframe3 : ∀ R, NotWrittenCpw R → σ3.regs.get? R = g R := fun R hR =>
    (frame_alu_cpw hobs3 R hR.x13 hR).trans (hframe2 R hR)
  -- STEP e30: sb a5,0(a2) → store byte 8p+0 at dst+8p+0
  obtain ⟨sb0, shlo0, shhi0, shwin0⟩ :=
    tail_sb_bounds dst src len p 0 (0x000#12) hreg hplo (by omega) sext_off0
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006e30 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006e30#64) vmi3
      (dst + BitVec.ofNat 64 (8*p)) (zero_extend (m := 64) (b0 : BitVec (8*1)))
      hG3 hpc3 hmi3 ha2_3 ha5_3 (by rw [hmem3eq]; exact hloaded) rfl shlo0 shhi0 shwin0 hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006e34#64 : BitVec 64) := by
    have := obs_store_pc hobs4; rwa [show BitVec.addInt (0x80006e30#64) 4 = (0x80006e34#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_store_other' hobs4 Register.x10 (by decide) ha0_3
  have ha2_4 := obs_store_other' hobs4 Register.x12 (by decide) ha2_3
  have ha1_4 := obs_store_other' hobs4 Register.x11 (by decide) ha1_3
  have hra_4 := obs_store_other' hobs4 Register.x1 (by decide) hra_3
  have ha5_4 := obs_store_other' hobs4 Register.x15 (by decide) ha5_3
  have ha4_4 := obs_store_other' hobs4 Register.x14 (by decide) ha4_3
  have ha3_4 := obs_store_other' hobs4 Register.x13 (by decide) ha3_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hloaded4 : StrcpyLoaded σ4.mem := by
    rw [hmem4, mem_afterNextPC, hmem3eq]
    refine strcpy_loaded_insert c.σ.mem _ _ ?_ hloaded
    have hcode := hreg.code_disjoint; rw [sb0]; omega
  have hb0eq : b0 = bs (8*p + 0) := hval 0 b0 (by omega) hb0m
  have hinv4 : MemInv dst src (len + 1) bs (8*p + 0 + 1) m0 σ4.mem := by
    rw [hmem4, mem_afterNextPC, hmem3eq, hb0eq]
    exact tail_meminv_store dst src len bs p 0 m0 c.σ.mem hreg (by omega) sb0 (by simpa using hinv0)
  have hframe4 : ∀ R, NotWrittenCpw R → σ4.regs.get? R = g R := fun R hR =>
    (frame_store_cpw hobs4 R hR).trans (hframe3 R hR)
  -- e34: beqz a5,0xe78  (a5 = zext (byte 8p+0)); taken iff off 0 = t
  by_cases hex0 : 8*p + 0 = len
  · have hbz : b0 = 0 := hbnul 0 b0 hex0 hb0m
    have hv : (zero_extend (m := 64) (b0 : BitVec (8*1)) == (0#64)) = true := by
      rw [zext_eq_zero_iff, hbz]; decide
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_80006e34_taken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006e34#64) vmi4
        (zero_extend (m := 64) (b0 : BitVec (8*1))) hG4 hpc4 hmi4 ha5_4 hloaded4 rfl hv hi4
    have hpc5 : σ5.regs.get? Register.PC = some (0x80006e78#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs5]; apply congrArg; apply BitVec.eq_of_toNat_eq; decide
    have ha0_5 := obs_btaken_other' hobs5 Register.x10 (by decide) ha0_4
    have hra_5 := obs_btaken_other' hobs5 Register.x1 (by decide) hra_4
    obtain ⟨vmi5, hmi5⟩ := obs_btaken_minstret hobs5
    have hinv5 : MemInv dst src (len + 1) bs (len + 1) m0 σ5.mem := by
      rw [hmem5]; have heq : 8*p + 0 + 1 = len + 1 := by omega
      rw [heq] at hinv4; exact hinv4
    obtain ⟨c', hsr, hpost⟩ := tail_ret g r dst src len m0 σ5.mem bs halign (0x80006e78#64)
      (Or.inl rfl) ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG5, by rw [hmem5]; exact hloaded4, hpc5, ha0_5, hra_5, ⟨vmi5, hmi5⟩, hi5, hinv5,
        fun R hR => (frame_btaken_cpw hobs5 R hR).trans (hframe4 R hR)⟩
    refine ⟨c', ?_, hpost⟩
    exact ((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans hsr)
  · -- e34 not taken (byte 8p+0 ≠ 0, i.e. 8p < len); fall through to e38
    have hlt0 : 8*p + 0 < len := by omega
    have hbz : b0 ≠ 0 := hbne 0 b0 hlt0 hb0m
    have hv : (zero_extend (m := 64) (b0 : BitVec (8*1)) == (0#64)) = false := by
      rw [zext_eq_zero_iff]; rw [beq_eq_false_iff_ne]; exact hbz
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_80006e34_nottaken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006e34#64) vmi4
        (zero_extend (m := 64) (b0 : BitVec (8*1))) hG4 hpc4 hmi4 ha5_4 hloaded4 rfl hv hi4
    have hpc5 : σ5.regs.get? Register.PC = some (0x80006e38#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs5
      rwa [show BitVec.addInt (0x80006e34#64) 4 = (0x80006e38#64 : BitVec 64) from by decide] at this
    have ha0_5 := obs_bnottaken_other' hobs5 Register.x10 (by decide) ha0_4
    have ha1_5 := obs_bnottaken_other' hobs5 Register.x11 (by decide) ha1_4
    have ha2_5 := obs_bnottaken_other' hobs5 Register.x12 (by decide) ha2_4
    have hra_5 := obs_bnottaken_other' hobs5 Register.x1 (by decide) hra_4
    have ha4_5 := obs_bnottaken_other' hobs5 Register.x14 (by decide) ha4_4
    have ha3_5 := obs_bnottaken_other' hobs5 Register.x13 (by decide) ha3_4
    obtain ⟨vmi5, hmi5⟩ := obs_bnottaken_minstret hobs5
    have hmem5eq : σ5.mem = σ4.mem := hmem5
    have hloaded5 : StrcpyLoaded σ5.mem := by rw [hmem5eq]; exact hloaded4
    have hinv5 : MemInv dst src (len + 1) bs (8*p + 1) m0 σ5.mem := by
      rw [hmem5eq]; have heq : 8*p + 0 + 1 = 8*p + 1 := by omega
      rw [heq] at hinv4; exact hinv4
    have hframe5 : ∀ R, NotWrittenCpw R → σ5.regs.get? R = g R := fun R hR =>
      (frame_bnottaken_cpw hobs5 R hR).trans (hframe4 R hR)
    have hsteps5 : Steps c ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ :=
      (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
        (Steps.single hs4)).trans (Steps.single hs5))
    -- STEP e38: sb a4,1(a2) → store byte 8p+1 at dst+8p+1
    have hb1eq : b1 = bs (8*p + 1) := hval 1 b1 (by omega) hb1m
    obtain ⟨sb1, shlo1, shhi1, shwin1⟩ :=
      tail_sb_bounds dst src len p 1 (0x001#12) hreg hplo (by omega) sext_off1
    obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
      site_80006e38 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006e38#64) vmi5
        (dst + BitVec.ofNat 64 (8*p)) (zero_extend (m := 64) (b1 : BitVec (8*1)))
        hG5 hpc5 hmi5 ha2_5 ha4_5 hloaded5 rfl shlo1 shhi1 shwin1 hi5
    have hpc6 : σ6.regs.get? Register.PC = some (0x80006e3c#64 : BitVec 64) := by
      have := obs_store_pc hobs6; rwa [show BitVec.addInt (0x80006e38#64) 4 = (0x80006e3c#64 : BitVec 64) from by decide] at this
    have ha0_6 := obs_store_other' hobs6 Register.x10 (by decide) ha0_5
    have ha1_6 := obs_store_other' hobs6 Register.x11 (by decide) ha1_5
    have ha2_6 := obs_store_other' hobs6 Register.x12 (by decide) ha2_5
    have hra_6 := obs_store_other' hobs6 Register.x1 (by decide) hra_5
    have ha4_6 := obs_store_other' hobs6 Register.x14 (by decide) ha4_5
    have ha3_6 := obs_store_other' hobs6 Register.x13 (by decide) ha3_5
    obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
    have hloaded6 : StrcpyLoaded σ6.mem := by
      rw [hmem6, mem_afterNextPC]
      refine strcpy_loaded_insert σ5.mem _ _ ?_ hloaded5
      have hcode := hreg.code_disjoint; rw [sb1]; omega
    have hinv6 : MemInv dst src (len + 1) bs (8*p + 1 + 1) m0 σ6.mem := by
      rw [hmem6, mem_afterNextPC, hb1eq]
      exact tail_meminv_store dst src len bs p 1 m0 σ5.mem hreg (by omega) sb1 (by simpa using hinv5)
    have hframe6 : ∀ R, NotWrittenCpw R → σ6.regs.get? R = g R := fun R hR =>
      (frame_store_cpw hobs6 R hR).trans (hframe5 R hR)
    have hsteps6 : Steps c ⟨σ6, i6, _⟩ := hsteps5.trans (Steps.single hs6)
    -- e3c: beqz a4,0xe78  (a4 = byte 8p+1); taken iff off 1 = t
    by_cases hex1 : 8*p + 1 = len
    · have hbz : b1 = 0 := hbnul 1 b1 hex1 hb1m
      have hv1 : (zero_extend (m := 64) (b1 : BitVec (8*1)) == (0#64)) = true := by
        rw [zext_eq_zero_iff, hbz]; decide
      obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
        site_80006e3c_taken σ6 i6 _ (0x80006e3c#64) vmi6
          (zero_extend (m := 64) (b1 : BitVec (8*1))) hG6 hpc6 hmi6 ha4_6 hloaded6 rfl hv1 hi6
      have hpc7 : σ7.regs.get? Register.PC = some (0x80006e78#64 : BitVec 64) := by
        rw [obs_btaken_pc hobs7]; apply congrArg; apply BitVec.eq_of_toNat_eq; decide
      have ha0_7 := obs_btaken_other' hobs7 Register.x10 (by decide) ha0_6
      have hra_7 := obs_btaken_other' hobs7 Register.x1 (by decide) hra_6
      obtain ⟨vmi7, hmi7⟩ := obs_btaken_minstret hobs7
      have hinv7 : MemInv dst src (len + 1) bs (len + 1) m0 σ7.mem := by
        rw [hmem7]; have heq : 8*p + 1 + 1 = len + 1 := by omega
        rw [heq] at hinv6; exact hinv6
      obtain ⟨c', hsr, hpost⟩ := tail_ret g r dst src len m0 σ7.mem bs halign (0x80006e78#64)
        (Or.inl rfl) ⟨σ7, i7, _⟩
        ⟨hG7, by rw [hmem7]; exact hloaded6, hpc7, ha0_7, hra_7, ⟨vmi7, hmi7⟩, hi7, hinv7,
          fun R hR => (frame_btaken_cpw hobs7 R hR).trans (hframe6 R hR)⟩
      exact ⟨c', (hsteps6.trans (Steps.single hs7)).trans hsr, hpost⟩
    · -- e3c not taken; continue to e40
      have hlt1 : 8*p + 1 < len := by omega
      have hbz : b1 ≠ 0 := hbne 1 b1 hlt1 hb1m
      have hv1 : (zero_extend (m := 64) (b1 : BitVec (8*1)) == (0#64)) = false := by
        rw [zext_eq_zero_iff, beq_eq_false_iff_ne]; exact hbz
      obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
        site_80006e3c_nottaken σ6 i6 _ (0x80006e3c#64) vmi6
          (zero_extend (m := 64) (b1 : BitVec (8*1))) hG6 hpc6 hmi6 ha4_6 hloaded6 rfl hv1 hi6
      have hpc7 : σ7.regs.get? Register.PC = some (0x80006e40#64 : BitVec 64) := by
        have := obs_bnottaken_pc hobs7
        rwa [show BitVec.addInt (0x80006e3c#64) 4 = (0x80006e40#64 : BitVec 64) from by decide] at this
      have ha0_7 := obs_bnottaken_other' hobs7 Register.x10 (by decide) ha0_6
      have ha1_7 := obs_bnottaken_other' hobs7 Register.x11 (by decide) ha1_6
      have ha2_7 := obs_bnottaken_other' hobs7 Register.x12 (by decide) ha2_6
      have hra_7 := obs_bnottaken_other' hobs7 Register.x1 (by decide) hra_6
      have ha3_7 := obs_bnottaken_other' hobs7 Register.x13 (by decide) ha3_6
      obtain ⟨vmi7, hmi7⟩ := obs_bnottaken_minstret hobs7
      have hmem7eq : σ7.mem = σ6.mem := hmem7
      have hloaded7 : StrcpyLoaded σ7.mem := by rw [hmem7eq]; exact hloaded6
      have hinv7 : MemInv dst src (len + 1) bs (8*p + 2) m0 σ7.mem := by
        rw [hmem7eq]; have heq : 8*p + 1 + 1 = 8*p + 2 := by omega
        rw [heq] at hinv6; exact hinv6
      have hframe7 : ∀ R, NotWrittenCpw R → σ7.regs.get? R = g R := fun R hR =>
        (frame_bnottaken_cpw hobs7 R hR).trans (hframe6 R hR)
      have hsteps7 : Steps c ⟨σ7, i7, _⟩ := hsteps6.trans (Steps.single hs7)
      -- STEP e40: lbu a5,3(a1) → a5 = zext (byte 8p+3)
      obtain ⟨b3, hb3m⟩ := hbyte 3 (by omega)
      have hb3cur : σ7.mem[(src.toNat + (8*p + 3))]? = some b3 :=
        tail_cur_byte dst src len _ m0 σ7.mem bs p 3 (by omega) hreg hplo hinv7 b3 hb3m
      obtain ⟨lb3, lhlo3, lhhi3, lhtif3⟩ :=
        wtail_lbu_bounds dst src len p 3 (0x003#12) hreg hplo (by omega) sext_off3
      obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
        site_80006e40 σ7 i7 _ (0x80006e40#64) vmi7 (src + BitVec.ofNat 64 (8*p)) b3
          hG7 hpc7 hmi7 ha1_7 hloaded7 rfl lhlo3 lhhi3 lhtif3
          (by rw [lb3]; simpa using hb3cur) hi7
      have hpc8 : σ8.regs.get? Register.PC = some (0x80006e44#64 : BitVec 64) := by
        have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80006e40#64) 4 = (0x80006e44#64 : BitVec 64) from by decide] at this
      have ha0_8 := obs_alu_other' hobs8 Register.x10 (by decide) ha0_7
      have ha1_8 := obs_alu_other' hobs8 Register.x11 (by decide) ha1_7
      have ha2_8 := obs_alu_other' hobs8 Register.x12 (by decide) ha2_7
      have hra_8 := obs_alu_other' hobs8 Register.x1 (by decide) hra_7
      have ha3_8 := obs_alu_other' hobs8 Register.x13 (by decide) ha3_7
      have ha5_8 : σ8.regs.get? Register.x15 = some (zero_extend (m := 64) (b3 : BitVec (8*1))) :=
        obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
      obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
      have hmem8eq : σ8.mem = σ7.mem := hmem8
      have hframe8 : ∀ R, NotWrittenCpw R → σ8.regs.get? R = g R := fun R hR =>
        (frame_alu_cpw hobs8 R hR.x15 hR).trans (hframe7 R hR)
      have hloaded8 : StrcpyLoaded σ8.mem := by rw [hmem8eq]; exact hloaded7
      have hinv8 : MemInv dst src (len + 1) bs (8*p + 2) m0 σ8.mem := by rw [hmem8eq]; exact hinv7
      have hsteps8 : Steps c ⟨σ8, i8, _⟩ := hsteps7.trans (Steps.single hs8)
      -- STEP e44: sb a3,2(a2) → store byte 8p+2 at dst+8p+2
      have hb2eq : b2 = bs (8*p + 2) := hval 2 b2 (by omega) hb2m
      obtain ⟨sb2, shlo2, shhi2, shwin2⟩ :=
        tail_sb_bounds dst src len p 2 (0x002#12) hreg hplo (by omega) sext_off2
      obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
        site_80006e44 σ8 i8 _ (0x80006e44#64) vmi8
          (dst + BitVec.ofNat 64 (8*p)) (zero_extend (m := 64) (b2 : BitVec (8*1)))
          hG8 hpc8 hmi8 ha2_8 ha3_8 hloaded8 rfl shlo2 shhi2 shwin2 hi8
      have hpc9 : σ9.regs.get? Register.PC = some (0x80006e48#64 : BitVec 64) := by
        have := obs_store_pc hobs9; rwa [show BitVec.addInt (0x80006e44#64) 4 = (0x80006e48#64 : BitVec 64) from by decide] at this
      have ha0_9 := obs_store_other' hobs9 Register.x10 (by decide) ha0_8
      have ha1_9 := obs_store_other' hobs9 Register.x11 (by decide) ha1_8
      have ha2_9 := obs_store_other' hobs9 Register.x12 (by decide) ha2_8
      have hra_9 := obs_store_other' hobs9 Register.x1 (by decide) hra_8
      have ha5_9 := obs_store_other' hobs9 Register.x15 (by decide) ha5_8
      have ha3_9 := obs_store_other' hobs9 Register.x13 (by decide) ha3_8
      obtain ⟨vmi9, hmi9⟩ := obs_store_minstret hobs9
      have hloaded9 : StrcpyLoaded σ9.mem := by
        rw [hmem9, mem_afterNextPC]
        refine strcpy_loaded_insert σ8.mem _ _ ?_ hloaded8
        have hcode := hreg.code_disjoint; rw [sb2]; omega
      have hinv9 : MemInv dst src (len + 1) bs (8*p + 2 + 1) m0 σ9.mem := by
        rw [hmem9, mem_afterNextPC, hb2eq]
        exact tail_meminv_store dst src len bs p 2 m0 σ8.mem hreg (by omega) sb2 (by simpa using hinv8)
      have hframe9 : ∀ R, NotWrittenCpw R → σ9.regs.get? R = g R := fun R hR =>
        (frame_store_cpw hobs9 R hR).trans (hframe8 R hR)
      have hsteps9 : Steps c ⟨σ9, i9, _⟩ := hsteps8.trans (Steps.single hs9)
      -- e48: beqz a3,0xe78  (a3 = byte 8p+2); taken iff off 2 = t
      by_cases hex2 : 8*p + 2 = len
      · have hbz : b2 = 0 := hbnul 2 b2 hex2 hb2m
        have hv2 : (zero_extend (m := 64) (b2 : BitVec (8*1)) == (0#64)) = true := by
          rw [zext_eq_zero_iff, hbz]; decide
        obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
          site_80006e48_taken σ9 i9 _ (0x80006e48#64) vmi9
            (zero_extend (m := 64) (b2 : BitVec (8*1))) hG9 hpc9 hmi9 ha3_9 hloaded9 rfl hv2 hi9
        have hpc10 : σ10.regs.get? Register.PC = some (0x80006e78#64 : BitVec 64) := by
          rw [obs_btaken_pc hobs10]; apply congrArg; apply BitVec.eq_of_toNat_eq; decide
        have ha0_10 := obs_btaken_other' hobs10 Register.x10 (by decide) ha0_9
        have hra_10 := obs_btaken_other' hobs10 Register.x1 (by decide) hra_9
        obtain ⟨vmi10, hmi10⟩ := obs_btaken_minstret hobs10
        have hinv10 : MemInv dst src (len + 1) bs (len + 1) m0 σ10.mem := by
          rw [hmem10]; have heq : 8*p + 2 + 1 = len + 1 := by omega
          rw [heq] at hinv9; exact hinv9
        obtain ⟨c', hsr, hpost⟩ := tail_ret g r dst src len m0 σ10.mem bs halign (0x80006e78#64)
          (Or.inl rfl) ⟨σ10, i10, _⟩
          ⟨hG10, by rw [hmem10]; exact hloaded9, hpc10, ha0_10, hra_10, ⟨vmi10, hmi10⟩, hi10, hinv10,
            fun R hR => (frame_btaken_cpw hobs10 R hR).trans (hframe9 R hR)⟩
        exact ⟨c', (hsteps9.trans (Steps.single hs10)).trans hsr, hpost⟩
      · -- e48 not taken; continue to e4c
        have hlt2 : 8*p + 2 < len := by omega
        have hbz : b2 ≠ 0 := hbne 2 b2 hlt2 hb2m
        have hv2 : (zero_extend (m := 64) (b2 : BitVec (8*1)) == (0#64)) = false := by
          rw [zext_eq_zero_iff, beq_eq_false_iff_ne]; exact hbz
        obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
          site_80006e48_nottaken σ9 i9 _ (0x80006e48#64) vmi9
            (zero_extend (m := 64) (b2 : BitVec (8*1))) hG9 hpc9 hmi9 ha3_9 hloaded9 rfl hv2 hi9
        have hpc10 : σ10.regs.get? Register.PC = some (0x80006e4c#64 : BitVec 64) := by
          have := obs_bnottaken_pc hobs10
          rwa [show BitVec.addInt (0x80006e48#64) 4 = (0x80006e4c#64 : BitVec 64) from by decide] at this
        have ha0_10 := obs_bnottaken_other' hobs10 Register.x10 (by decide) ha0_9
        have ha1_10 := obs_bnottaken_other' hobs10 Register.x11 (by decide) ha1_9
        have ha2_10 := obs_bnottaken_other' hobs10 Register.x12 (by decide) ha2_9
        have hra_10 := obs_bnottaken_other' hobs10 Register.x1 (by decide) hra_9
        have ha5_10 := obs_bnottaken_other' hobs10 Register.x15 (by decide) ha5_9
        obtain ⟨vmi10, hmi10⟩ := obs_bnottaken_minstret hobs10
        have hmem10eq : σ10.mem = σ9.mem := hmem10
        have hloaded10 : StrcpyLoaded σ10.mem := by rw [hmem10eq]; exact hloaded9
        have hinv10 : MemInv dst src (len + 1) bs (8*p + 3) m0 σ10.mem := by
          rw [hmem10eq]; have heq : 8*p + 2 + 1 = 8*p + 3 := by omega
          rw [heq] at hinv9; exact hinv9
        have hframe10 : ∀ R, NotWrittenCpw R → σ10.regs.get? R = g R := fun R hR =>
          (frame_bnottaken_cpw hobs10 R hR).trans (hframe9 R hR)
        have hsteps10 : Steps c ⟨σ10, i10, _⟩ := hsteps9.trans (Steps.single hs10)
        -- STEP e4c: lbu a4,4(a1) → a4 = zext (byte 8p+4)
        obtain ⟨b4, hb4m⟩ := hbyte 4 (by omega)
        have hb4cur : σ10.mem[(src.toNat + (8*p + 4))]? = some b4 :=
          tail_cur_byte dst src len _ m0 σ10.mem bs p 4 (by omega) hreg hplo hinv10 b4 hb4m
        obtain ⟨lb4, lhlo4, lhhi4, lhtif4⟩ :=
          wtail_lbu_bounds dst src len p 4 (0x004#12) hreg hplo (by omega) sext_off4
        obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
          site_80006e4c σ10 i10 _ (0x80006e4c#64) vmi10 (src + BitVec.ofNat 64 (8*p)) b4
            hG10 hpc10 hmi10 ha1_10 hloaded10 rfl lhlo4 lhhi4 lhtif4
            (by rw [lb4]; simpa using hb4cur) hi10
        have hpc11 : σ11.regs.get? Register.PC = some (0x80006e50#64 : BitVec 64) := by
          have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80006e4c#64) 4 = (0x80006e50#64 : BitVec 64) from by decide] at this
        have ha0_11 := obs_alu_other' hobs11 Register.x10 (by decide) ha0_10
        have ha1_11 := obs_alu_other' hobs11 Register.x11 (by decide) ha1_10
        have ha2_11 := obs_alu_other' hobs11 Register.x12 (by decide) ha2_10
        have hra_11 := obs_alu_other' hobs11 Register.x1 (by decide) hra_10
        have ha5_11 := obs_alu_other' hobs11 Register.x15 (by decide) ha5_10
        have ha4_11 : σ11.regs.get? Register.x14 = some (zero_extend (m := 64) (b4 : BitVec (8*1))) :=
          obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
        obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
        have hmem11eq : σ11.mem = σ10.mem := hmem11
        have hloaded11 : StrcpyLoaded σ11.mem := by rw [hmem11eq]; exact hloaded10
        have hinv11 : MemInv dst src (len + 1) bs (8*p + 3) m0 σ11.mem := by rw [hmem11eq]; exact hinv10
        have hframe11 : ∀ R, NotWrittenCpw R → σ11.regs.get? R = g R := fun R hR =>
          (frame_alu_cpw hobs11 R hR.x14 hR).trans (hframe10 R hR)
        have hsteps11 : Steps c ⟨σ11, i11, _⟩ := hsteps10.trans (Steps.single hs11)
        -- STEP e50: sb a5,3(a2) → store byte 8p+3 at dst+8p+3
        have hb3eq : b3 = bs (8*p + 3) := hval 3 b3 (by omega) hb3m
        obtain ⟨sb3, shlo3, shhi3, shwin3⟩ :=
          tail_sb_bounds dst src len p 3 (0x003#12) hreg hplo (by omega) sext_off3
        obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
          site_80006e50 σ11 i11 _ (0x80006e50#64) vmi11
            (dst + BitVec.ofNat 64 (8*p)) (zero_extend (m := 64) (b3 : BitVec (8*1)))
            hG11 hpc11 hmi11 ha2_11 ha5_11 hloaded11 rfl shlo3 shhi3 shwin3 hi11
        have hpc12 : σ12.regs.get? Register.PC = some (0x80006e54#64 : BitVec 64) := by
          have := obs_store_pc hobs12; rwa [show BitVec.addInt (0x80006e50#64) 4 = (0x80006e54#64 : BitVec 64) from by decide] at this
        have ha0_12 := obs_store_other' hobs12 Register.x10 (by decide) ha0_11
        have ha1_12 := obs_store_other' hobs12 Register.x11 (by decide) ha1_11
        have ha2_12 := obs_store_other' hobs12 Register.x12 (by decide) ha2_11
        have hra_12 := obs_store_other' hobs12 Register.x1 (by decide) hra_11
        have ha5_12 := obs_store_other' hobs12 Register.x15 (by decide) ha5_11
        have ha4_12 := obs_store_other' hobs12 Register.x14 (by decide) ha4_11
        obtain ⟨vmi12, hmi12⟩ := obs_store_minstret hobs12
        have hloaded12 : StrcpyLoaded σ12.mem := by
          rw [hmem12, mem_afterNextPC]
          refine strcpy_loaded_insert σ11.mem _ _ ?_ hloaded11
          have hcode := hreg.code_disjoint; rw [sb3]; omega
        have hinv12 : MemInv dst src (len + 1) bs (8*p + 3 + 1) m0 σ12.mem := by
          rw [hmem12, mem_afterNextPC, hb3eq]
          exact tail_meminv_store dst src len bs p 3 m0 σ11.mem hreg (by omega) sb3 (by simpa using hinv11)
        have hframe12 : ∀ R, NotWrittenCpw R → σ12.regs.get? R = g R := fun R hR =>
          (frame_store_cpw hobs12 R hR).trans (hframe11 R hR)
        have hsteps12 : Steps c ⟨σ12, i12, _⟩ := hsteps11.trans (Steps.single hs12)
        -- e54: beqz a5,0xe78 (a5 = byte 8p+3); taken iff off 3 = t
        by_cases hex3 : 8*p + 3 = len
        · have hbz : b3 = 0 := hbnul 3 b3 hex3 hb3m
          have hv3 : (zero_extend (m := 64) (b3 : BitVec (8*1)) == (0#64)) = true := by
            rw [zext_eq_zero_iff, hbz]; decide
          obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
            site_80006e54_taken σ12 i12 _ (0x80006e54#64) vmi12
              (zero_extend (m := 64) (b3 : BitVec (8*1))) hG12 hpc12 hmi12 ha5_12 hloaded12 rfl hv3 hi12
          have hpc13 : σ13.regs.get? Register.PC = some (0x80006e78#64 : BitVec 64) := by
            rw [obs_btaken_pc hobs13]; apply congrArg; apply BitVec.eq_of_toNat_eq; decide
          have ha0_13 := obs_btaken_other' hobs13 Register.x10 (by decide) ha0_12
          have hra_13 := obs_btaken_other' hobs13 Register.x1 (by decide) hra_12
          obtain ⟨vmi13, hmi13⟩ := obs_btaken_minstret hobs13
          have hinv13 : MemInv dst src (len + 1) bs (len + 1) m0 σ13.mem := by
            rw [hmem13]; have heq : 8*p + 3 + 1 = len + 1 := by omega
            rw [heq] at hinv12; exact hinv12
          obtain ⟨c', hsr, hpost⟩ := tail_ret g r dst src len m0 σ13.mem bs halign (0x80006e78#64)
            (Or.inl rfl) ⟨σ13, i13, _⟩
            ⟨hG13, by rw [hmem13]; exact hloaded12, hpc13, ha0_13, hra_13, ⟨vmi13, hmi13⟩, hi13, hinv13,
              fun R hR => (frame_btaken_cpw hobs13 R hR).trans (hframe12 R hR)⟩
          exact ⟨c', (hsteps12.trans (Steps.single hs13)).trans hsr, hpost⟩
        · -- e54 not taken; continue to e58
          have hlt3 : 8*p + 3 < len := by omega
          have hbz : b3 ≠ 0 := hbne 3 b3 hlt3 hb3m
          have hv3 : (zero_extend (m := 64) (b3 : BitVec (8*1)) == (0#64)) = false := by
            rw [zext_eq_zero_iff, beq_eq_false_iff_ne]; exact hbz
          obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
            site_80006e54_nottaken σ12 i12 _ (0x80006e54#64) vmi12
              (zero_extend (m := 64) (b3 : BitVec (8*1))) hG12 hpc12 hmi12 ha5_12 hloaded12 rfl hv3 hi12
          have hpc13 : σ13.regs.get? Register.PC = some (0x80006e58#64 : BitVec 64) := by
            have := obs_bnottaken_pc hobs13
            rwa [show BitVec.addInt (0x80006e54#64) 4 = (0x80006e58#64 : BitVec 64) from by decide] at this
          have ha0_13 := obs_bnottaken_other' hobs13 Register.x10 (by decide) ha0_12
          have ha1_13 := obs_bnottaken_other' hobs13 Register.x11 (by decide) ha1_12
          have ha2_13 := obs_bnottaken_other' hobs13 Register.x12 (by decide) ha2_12
          have hra_13 := obs_bnottaken_other' hobs13 Register.x1 (by decide) hra_12
          have ha4_13 := obs_bnottaken_other' hobs13 Register.x14 (by decide) ha4_12
          obtain ⟨vmi13, hmi13⟩ := obs_bnottaken_minstret hobs13
          have hmem13eq : σ13.mem = σ12.mem := hmem13
          have hloaded13 : StrcpyLoaded σ13.mem := by rw [hmem13eq]; exact hloaded12
          have hinv13 : MemInv dst src (len + 1) bs (8*p + 4) m0 σ13.mem := by
            rw [hmem13eq]; have heq : 8*p + 3 + 1 = 8*p + 4 := by omega
            rw [heq] at hinv12; exact hinv12
          have hframe13 : ∀ R, NotWrittenCpw R → σ13.regs.get? R = g R := fun R hR =>
            (frame_bnottaken_cpw hobs13 R hR).trans (hframe12 R hR)
          have hsteps13 : Steps c ⟨σ13, i13, _⟩ := hsteps12.trans (Steps.single hs13)
          -- STEP e58: lbu a5,5(a1) → a5 = zext (byte 8p+5)
          obtain ⟨b5, hb5m⟩ := hbyte 5 (by omega)
          have hb5cur : σ13.mem[(src.toNat + (8*p + 5))]? = some b5 :=
            tail_cur_byte dst src len _ m0 σ13.mem bs p 5 (by omega) hreg hplo hinv13 b5 hb5m
          obtain ⟨lb5, lhlo5, lhhi5, lhtif5⟩ :=
            wtail_lbu_bounds dst src len p 5 (0x005#12) hreg hplo (by omega) sext_off5
          obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
            site_80006e58 σ13 i13 _ (0x80006e58#64) vmi13 (src + BitVec.ofNat 64 (8*p)) b5
              hG13 hpc13 hmi13 ha1_13 hloaded13 rfl lhlo5 lhhi5 lhtif5
              (by rw [lb5]; simpa using hb5cur) hi13
          have hpc14 : σ14.regs.get? Register.PC = some (0x80006e5c#64 : BitVec 64) := by
            have := obs_alu_pc hobs14; rwa [show BitVec.addInt (0x80006e58#64) 4 = (0x80006e5c#64 : BitVec 64) from by decide] at this
          have ha0_14 := obs_alu_other' hobs14 Register.x10 (by decide) ha0_13
          have ha1_14 := obs_alu_other' hobs14 Register.x11 (by decide) ha1_13
          have ha2_14 := obs_alu_other' hobs14 Register.x12 (by decide) ha2_13
          have hra_14 := obs_alu_other' hobs14 Register.x1 (by decide) hra_13
          have ha4_14 := obs_alu_other' hobs14 Register.x14 (by decide) ha4_13
          have ha5_14 : σ14.regs.get? Register.x15 = some (zero_extend (m := 64) (b5 : BitVec (8*1))) :=
            obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
          obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
          have hmem14eq : σ14.mem = σ13.mem := hmem14
          have hloaded14 : StrcpyLoaded σ14.mem := by rw [hmem14eq]; exact hloaded13
          have hinv14 : MemInv dst src (len + 1) bs (8*p + 4) m0 σ14.mem := by rw [hmem14eq]; exact hinv13
          have hframe14 : ∀ R, NotWrittenCpw R → σ14.regs.get? R = g R := fun R hR =>
            (frame_alu_cpw hobs14 R hR.x15 hR).trans (hframe13 R hR)
          have hsteps14 : Steps c ⟨σ14, i14, _⟩ := hsteps13.trans (Steps.single hs14)
          -- STEP e5c: sb a4,4(a2) → store byte 8p+4 at dst+8p+4
          have hb4eq : b4 = bs (8*p + 4) := hval 4 b4 (by omega) hb4m
          obtain ⟨sb4, shlo4, shhi4, shwin4⟩ :=
            tail_sb_bounds dst src len p 4 (0x004#12) hreg hplo (by omega) sext_off4
          obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
            site_80006e5c σ14 i14 _ (0x80006e5c#64) vmi14
              (dst + BitVec.ofNat 64 (8*p)) (zero_extend (m := 64) (b4 : BitVec (8*1)))
              hG14 hpc14 hmi14 ha2_14 ha4_14 hloaded14 rfl shlo4 shhi4 shwin4 hi14
          have hpc15 : σ15.regs.get? Register.PC = some (0x80006e60#64 : BitVec 64) := by
            have := obs_store_pc hobs15; rwa [show BitVec.addInt (0x80006e5c#64) 4 = (0x80006e60#64 : BitVec 64) from by decide] at this
          have ha0_15 := obs_store_other' hobs15 Register.x10 (by decide) ha0_14
          have ha1_15 := obs_store_other' hobs15 Register.x11 (by decide) ha1_14
          have ha2_15 := obs_store_other' hobs15 Register.x12 (by decide) ha2_14
          have hra_15 := obs_store_other' hobs15 Register.x1 (by decide) hra_14
          have ha5_15 := obs_store_other' hobs15 Register.x15 (by decide) ha5_14
          have ha4_15 := obs_store_other' hobs15 Register.x14 (by decide) ha4_14
          obtain ⟨vmi15, hmi15⟩ := obs_store_minstret hobs15
          have hloaded15 : StrcpyLoaded σ15.mem := by
            rw [hmem15, mem_afterNextPC]
            refine strcpy_loaded_insert σ14.mem _ _ ?_ hloaded14
            have hcode := hreg.code_disjoint; rw [sb4]; omega
          have hinv15 : MemInv dst src (len + 1) bs (8*p + 4 + 1) m0 σ15.mem := by
            rw [hmem15, mem_afterNextPC, hb4eq]
            exact tail_meminv_store dst src len bs p 4 m0 σ14.mem hreg (by omega) sb4 (by simpa using hinv14)
          have hframe15 : ∀ R, NotWrittenCpw R → σ15.regs.get? R = g R := fun R hR =>
            (frame_store_cpw hobs15 R hR).trans (hframe14 R hR)
          have hsteps15 : Steps c ⟨σ15, i15, _⟩ := hsteps14.trans (Steps.single hs15)
          -- e60: beqz a4,0xe78 (a4 = byte 8p+4); taken iff off 4 = t
          by_cases hex4 : 8*p + 4 = len
          · have hbz : b4 = 0 := hbnul 4 b4 hex4 hb4m
            have hv4 : (zero_extend (m := 64) (b4 : BitVec (8*1)) == (0#64)) = true := by
              rw [zext_eq_zero_iff, hbz]; decide
            obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
              site_80006e60_taken σ15 i15 _ (0x80006e60#64) vmi15
                (zero_extend (m := 64) (b4 : BitVec (8*1))) hG15 hpc15 hmi15 ha4_15 hloaded15 rfl hv4 hi15
            have hpc16 : σ16.regs.get? Register.PC = some (0x80006e78#64 : BitVec 64) := by
              rw [obs_btaken_pc hobs16]; apply congrArg; apply BitVec.eq_of_toNat_eq; decide
            have ha0_16 := obs_btaken_other' hobs16 Register.x10 (by decide) ha0_15
            have hra_16 := obs_btaken_other' hobs16 Register.x1 (by decide) hra_15
            obtain ⟨vmi16, hmi16⟩ := obs_btaken_minstret hobs16
            have hinv16 : MemInv dst src (len + 1) bs (len + 1) m0 σ16.mem := by
              rw [hmem16]; have heq : 8*p + 4 + 1 = len + 1 := by omega
              rw [heq] at hinv15; exact hinv15
            obtain ⟨c', hsr, hpost⟩ := tail_ret g r dst src len m0 σ16.mem bs halign (0x80006e78#64)
              (Or.inl rfl) ⟨σ16, i16, _⟩
              ⟨hG16, by rw [hmem16]; exact hloaded15, hpc16, ha0_16, hra_16, ⟨vmi16, hmi16⟩, hi16, hinv16,
                fun R hR => (frame_btaken_cpw hobs16 R hR).trans (hframe15 R hR)⟩
            exact ⟨c', (hsteps15.trans (Steps.single hs16)).trans hsr, hpost⟩
          · -- e60 not taken; continue to e64
            have hlt4 : 8*p + 4 < len := by omega
            have hbz : b4 ≠ 0 := hbne 4 b4 hlt4 hb4m
            have hv4 : (zero_extend (m := 64) (b4 : BitVec (8*1)) == (0#64)) = false := by
              rw [zext_eq_zero_iff, beq_eq_false_iff_ne]; exact hbz
            obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
              site_80006e60_nottaken σ15 i15 _ (0x80006e60#64) vmi15
                (zero_extend (m := 64) (b4 : BitVec (8*1))) hG15 hpc15 hmi15 ha4_15 hloaded15 rfl hv4 hi15
            have hpc16 : σ16.regs.get? Register.PC = some (0x80006e64#64 : BitVec 64) := by
              have := obs_bnottaken_pc hobs16
              rwa [show BitVec.addInt (0x80006e60#64) 4 = (0x80006e64#64 : BitVec 64) from by decide] at this
            have ha0_16 := obs_bnottaken_other' hobs16 Register.x10 (by decide) ha0_15
            have ha1_16 := obs_bnottaken_other' hobs16 Register.x11 (by decide) ha1_15
            have ha2_16 := obs_bnottaken_other' hobs16 Register.x12 (by decide) ha2_15
            have hra_16 := obs_bnottaken_other' hobs16 Register.x1 (by decide) hra_15
            have ha5_16 := obs_bnottaken_other' hobs16 Register.x15 (by decide) ha5_15
            obtain ⟨vmi16, hmi16⟩ := obs_bnottaken_minstret hobs16
            have hmem16eq : σ16.mem = σ15.mem := hmem16
            have hloaded16 : StrcpyLoaded σ16.mem := by rw [hmem16eq]; exact hloaded15
            have hinv16 : MemInv dst src (len + 1) bs (8*p + 5) m0 σ16.mem := by
              rw [hmem16eq]; have heq : 8*p + 4 + 1 = 8*p + 5 := by omega
              rw [heq] at hinv15; exact hinv15
            have hframe16 : ∀ R, NotWrittenCpw R → σ16.regs.get? R = g R := fun R hR =>
              (frame_bnottaken_cpw hobs16 R hR).trans (hframe15 R hR)
            have hsteps16 : Steps c ⟨σ16, i16, _⟩ := hsteps15.trans (Steps.single hs16)
            -- STEP e64: lbu a4,6(a1) → a4 = zext (byte 8p+6)
            obtain ⟨b6, hb6m⟩ := hbyte 6 (by omega)
            have hb6cur : σ16.mem[(src.toNat + (8*p + 6))]? = some b6 :=
              tail_cur_byte dst src len _ m0 σ16.mem bs p 6 (by omega) hreg hplo hinv16 b6 hb6m
            obtain ⟨lb6, lhlo6, lhhi6, lhtif6⟩ :=
              wtail_lbu_bounds dst src len p 6 (0x006#12) hreg hplo (by omega) sext_off6
            obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
              site_80006e64 σ16 i16 _ (0x80006e64#64) vmi16 (src + BitVec.ofNat 64 (8*p)) b6
                hG16 hpc16 hmi16 ha1_16 hloaded16 rfl lhlo6 lhhi6 lhtif6
                (by rw [lb6]; simpa using hb6cur) hi16
            have hpc17 : σ17.regs.get? Register.PC = some (0x80006e68#64 : BitVec 64) := by
              have := obs_alu_pc hobs17; rwa [show BitVec.addInt (0x80006e64#64) 4 = (0x80006e68#64 : BitVec 64) from by decide] at this
            have ha0_17 := obs_alu_other' hobs17 Register.x10 (by decide) ha0_16
            have ha1_17 := obs_alu_other' hobs17 Register.x11 (by decide) ha1_16
            have ha2_17 := obs_alu_other' hobs17 Register.x12 (by decide) ha2_16
            have hra_17 := obs_alu_other' hobs17 Register.x1 (by decide) hra_16
            have ha5_17 := obs_alu_other' hobs17 Register.x15 (by decide) ha5_16
            have ha4_17 : σ17.regs.get? Register.x14 = some (zero_extend (m := 64) (b6 : BitVec (8*1))) :=
              obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide)
            obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
            have hmem17eq : σ17.mem = σ16.mem := hmem17
            have hloaded17 : StrcpyLoaded σ17.mem := by rw [hmem17eq]; exact hloaded16
            have hinv17 : MemInv dst src (len + 1) bs (8*p + 5) m0 σ17.mem := by rw [hmem17eq]; exact hinv16
            have hframe17 : ∀ R, NotWrittenCpw R → σ17.regs.get? R = g R := fun R hR =>
              (frame_alu_cpw hobs17 R hR.x14 hR).trans (hframe16 R hR)
            have hsteps17 : Steps c ⟨σ17, i17, _⟩ := hsteps16.trans (Steps.single hs17)
            -- STEP e68: sb a5,5(a2) → store byte 8p+5 at dst+8p+5
            have hb5eq : b5 = bs (8*p + 5) := hval 5 b5 (by omega) hb5m
            obtain ⟨sb5, shlo5, shhi5, shwin5⟩ :=
              tail_sb_bounds dst src len p 5 (0x005#12) hreg hplo (by omega) sext_off5
            obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
              site_80006e68 σ17 i17 _ (0x80006e68#64) vmi17
                (dst + BitVec.ofNat 64 (8*p)) (zero_extend (m := 64) (b5 : BitVec (8*1)))
                hG17 hpc17 hmi17 ha2_17 ha5_17 hloaded17 rfl shlo5 shhi5 shwin5 hi17
            have hpc18 : σ18.regs.get? Register.PC = some (0x80006e6c#64 : BitVec 64) := by
              have := obs_store_pc hobs18; rwa [show BitVec.addInt (0x80006e68#64) 4 = (0x80006e6c#64 : BitVec 64) from by decide] at this
            have ha0_18 := obs_store_other' hobs18 Register.x10 (by decide) ha0_17
            have ha1_18 := obs_store_other' hobs18 Register.x11 (by decide) ha1_17
            have ha2_18 := obs_store_other' hobs18 Register.x12 (by decide) ha2_17
            have hra_18 := obs_store_other' hobs18 Register.x1 (by decide) hra_17
            have ha4_18 := obs_store_other' hobs18 Register.x14 (by decide) ha4_17
            have ha5_18 := obs_store_other' hobs18 Register.x15 (by decide) ha5_17
            obtain ⟨vmi18, hmi18⟩ := obs_store_minstret hobs18
            have hloaded18 : StrcpyLoaded σ18.mem := by
              rw [hmem18, mem_afterNextPC]
              refine strcpy_loaded_insert σ17.mem _ _ ?_ hloaded17
              have hcode := hreg.code_disjoint; rw [sb5]; omega
            have hinv18 : MemInv dst src (len + 1) bs (8*p + 5 + 1) m0 σ18.mem := by
              rw [hmem18, mem_afterNextPC, hb5eq]
              exact tail_meminv_store dst src len bs p 5 m0 σ17.mem hreg (by omega) sb5 (by simpa using hinv17)
            have hframe18 : ∀ R, NotWrittenCpw R → σ18.regs.get? R = g R := fun R hR =>
              (frame_store_cpw hobs18 R hR).trans (hframe17 R hR)
            have hsteps18 : Steps c ⟨σ18, i18, _⟩ := hsteps17.trans (Steps.single hs18)
            -- e6c: beqz a5,0xe78 (a5 = byte 8p+5); taken iff off 5 = t
            by_cases hex5 : 8*p + 5 = len
            · have hbz : b5 = 0 := hbnul 5 b5 hex5 hb5m
              have hv5 : (zero_extend (m := 64) (b5 : BitVec (8*1)) == (0#64)) = true := by
                rw [zext_eq_zero_iff, hbz]; decide
              obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
                site_80006e6c_taken σ18 i18 _ (0x80006e6c#64) vmi18
                  (zero_extend (m := 64) (b5 : BitVec (8*1))) hG18 hpc18 hmi18 ha5_18 hloaded18 rfl hv5 hi18
              have hpc19 : σ19.regs.get? Register.PC = some (0x80006e78#64 : BitVec 64) := by
                rw [obs_btaken_pc hobs19]; apply congrArg; apply BitVec.eq_of_toNat_eq; decide
              have ha0_19 := obs_btaken_other' hobs19 Register.x10 (by decide) ha0_18
              have hra_19 := obs_btaken_other' hobs19 Register.x1 (by decide) hra_18
              obtain ⟨vmi19, hmi19⟩ := obs_btaken_minstret hobs19
              have hinv19 : MemInv dst src (len + 1) bs (len + 1) m0 σ19.mem := by
                rw [hmem19]; have heq : 8*p + 5 + 1 = len + 1 := by omega
                rw [heq] at hinv18; exact hinv18
              obtain ⟨c', hsr, hpost⟩ := tail_ret g r dst src len m0 σ19.mem bs halign (0x80006e78#64)
                (Or.inl rfl) ⟨σ19, i19, _⟩
                ⟨hG19, by rw [hmem19]; exact hloaded18, hpc19, ha0_19, hra_19, ⟨vmi19, hmi19⟩, hi19, hinv19,
                  fun R hR => (frame_btaken_cpw hobs19 R hR).trans (hframe18 R hR)⟩
              exact ⟨c', (hsteps18.trans (Steps.single hs19)).trans hsr, hpost⟩
            · -- e6c not taken; continue to e70 (t ∈ {6,7})
              have hlt5 : 8*p + 5 < len := by omega
              have hbz : b5 ≠ 0 := hbne 5 b5 hlt5 hb5m
              have hv5 : (zero_extend (m := 64) (b5 : BitVec (8*1)) == (0#64)) = false := by
                rw [zext_eq_zero_iff, beq_eq_false_iff_ne]; exact hbz
              obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
                site_80006e6c_nottaken σ18 i18 _ (0x80006e6c#64) vmi18
                  (zero_extend (m := 64) (b5 : BitVec (8*1))) hG18 hpc18 hmi18 ha5_18 hloaded18 rfl hv5 hi18
              have hpc19 : σ19.regs.get? Register.PC = some (0x80006e70#64 : BitVec 64) := by
                have := obs_bnottaken_pc hobs19
                rwa [show BitVec.addInt (0x80006e6c#64) 4 = (0x80006e70#64 : BitVec 64) from by decide] at this
              have ha0_19 := obs_bnottaken_other' hobs19 Register.x10 (by decide) ha0_18
              have ha1_19 := obs_bnottaken_other' hobs19 Register.x11 (by decide) ha1_18
              have ha2_19 := obs_bnottaken_other' hobs19 Register.x12 (by decide) ha2_18
              have hra_19 := obs_bnottaken_other' hobs19 Register.x1 (by decide) hra_18
              have ha4_19 := obs_bnottaken_other' hobs19 Register.x14 (by decide) ha4_18
              obtain ⟨vmi19, hmi19⟩ := obs_bnottaken_minstret hobs19
              have hmem19eq : σ19.mem = σ18.mem := hmem19
              have hloaded19 : StrcpyLoaded σ19.mem := by rw [hmem19eq]; exact hloaded18
              have hinv19 : MemInv dst src (len + 1) bs (8*p + 6) m0 σ19.mem := by
                rw [hmem19eq]; have heq : 8*p + 5 + 1 = 8*p + 6 := by omega
                rw [heq] at hinv18; exact hinv18
              have hframe19 : ∀ R, NotWrittenCpw R → σ19.regs.get? R = g R := fun R hR =>
                (frame_bnottaken_cpw hobs19 R hR).trans (hframe18 R hR)
              have hsteps19 : Steps c ⟨σ19, i19, _⟩ := hsteps18.trans (Steps.single hs19)
              -- STEP e70: sb a4,6(a2) → store byte 8p+6 at dst+8p+6
              have hb6eq : b6 = bs (8*p + 6) := hval 6 b6 (by omega) hb6m
              obtain ⟨sb6, shlo6, shhi6, shwin6⟩ :=
                tail_sb_bounds dst src len p 6 (0x006#12) hreg hplo (by omega) sext_off6
              obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
                site_80006e70 σ19 i19 _ (0x80006e70#64) vmi19
                  (dst + BitVec.ofNat 64 (8*p)) (zero_extend (m := 64) (b6 : BitVec (8*1)))
                  hG19 hpc19 hmi19 ha2_19 ha4_19 hloaded19 rfl shlo6 shhi6 shwin6 hi19
              have hpc20 : σ20.regs.get? Register.PC = some (0x80006e74#64 : BitVec 64) := by
                have := obs_store_pc hobs20; rwa [show BitVec.addInt (0x80006e70#64) 4 = (0x80006e74#64 : BitVec 64) from by decide] at this
              have ha0_20 := obs_store_other' hobs20 Register.x10 (by decide) ha0_19
              have ha1_20 := obs_store_other' hobs20 Register.x11 (by decide) ha1_19
              have ha2_20 := obs_store_other' hobs20 Register.x12 (by decide) ha2_19
              have hra_20 := obs_store_other' hobs20 Register.x1 (by decide) hra_19
              have ha4_20 := obs_store_other' hobs20 Register.x14 (by decide) ha4_19
              obtain ⟨vmi20, hmi20⟩ := obs_store_minstret hobs20
              have hloaded20 : StrcpyLoaded σ20.mem := by
                rw [hmem20, mem_afterNextPC]
                refine strcpy_loaded_insert σ19.mem _ _ ?_ hloaded19
                have hcode := hreg.code_disjoint; rw [sb6]; omega
              have hinv20 : MemInv dst src (len + 1) bs (8*p + 6 + 1) m0 σ20.mem := by
                rw [hmem20, mem_afterNextPC, hb6eq]
                exact tail_meminv_store dst src len bs p 6 m0 σ19.mem hreg (by omega) sb6 (by simpa using hinv19)
              have hframe20 : ∀ R, NotWrittenCpw R → σ20.regs.get? R = g R := fun R hR =>
                (frame_store_cpw hobs20 R hR).trans (hframe19 R hR)
              have hsteps20 : Steps c ⟨σ20, i20, _⟩ := hsteps19.trans (Steps.single hs20)
              -- e74: bnez a4,0xe98 (a4 = byte 8p+6); taken iff off 6 ≠ t, i.e. t = 7
              by_cases hex6 : 8*p + 6 = len
              · -- t = 6: bnez NOT taken (byte 8p+6 = 0), fall through to e78 ret
                have hbz : b6 = 0 := hbnul 6 b6 hex6 hb6m
                have hv6 : (zero_extend (m := 64) (b6 : BitVec (8*1)) != (0#64)) = false := by
                  rw [zext_ne_zero_iff, hbz]; decide
                obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
                  site_80006e74_nottaken σ20 i20 _ (0x80006e74#64) vmi20
                    (zero_extend (m := 64) (b6 : BitVec (8*1))) hG20 hpc20 hmi20 ha4_20 hloaded20 rfl hv6 hi20
                have hpc21 : σ21.regs.get? Register.PC = some (0x80006e78#64 : BitVec 64) := by
                  have := obs_bnottaken_pc hobs21
                  rwa [show BitVec.addInt (0x80006e74#64) 4 = (0x80006e78#64 : BitVec 64) from by decide] at this
                have ha0_21 := obs_bnottaken_other' hobs21 Register.x10 (by decide) ha0_20
                have hra_21 := obs_bnottaken_other' hobs21 Register.x1 (by decide) hra_20
                obtain ⟨vmi21, hmi21⟩ := obs_bnottaken_minstret hobs21
                have hmem21eq : σ21.mem = σ20.mem := hmem21
                have hinv21 : MemInv dst src (len + 1) bs (len + 1) m0 σ21.mem := by
                  rw [hmem21eq]; have heq : 8*p + 6 + 1 = len + 1 := by omega
                  rw [heq] at hinv20; exact hinv20
                obtain ⟨c', hsr, hpost⟩ := tail_ret g r dst src len m0 σ21.mem bs halign (0x80006e78#64)
                  (Or.inl rfl) ⟨σ21, i21, _⟩
                  ⟨hG21, by rw [hmem21eq]; exact hloaded20, hpc21, ha0_21, hra_21, ⟨vmi21, hmi21⟩, hi21, hinv21,
                    fun R hR => (frame_bnottaken_cpw hobs21 R hR).trans (hframe20 R hR)⟩
                exact ⟨c', (hsteps20.trans (Steps.single hs21)).trans hsr, hpost⟩
              · -- t = 7: bnez taken (byte 8p+6 ≠ 0), jump to e98 finisher
                have hlt6 : 8*p + 6 < len := by omega
                have ht7 : 8*p + 7 = len := by omega
                have hbz : b6 ≠ 0 := hbne 6 b6 hlt6 hb6m
                have hv6 : (zero_extend (m := 64) (b6 : BitVec (8*1)) != (0#64)) = true := by
                  rw [zext_ne_zero_iff]; rw [bne_iff_ne]; exact hbz
                obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
                  site_80006e74_taken σ20 i20 _ (0x80006e74#64) vmi20
                    (zero_extend (m := 64) (b6 : BitVec (8*1))) hG20 hpc20 hmi20 ha4_20 hloaded20 rfl hv6 hi20
                have hpc21 : σ21.regs.get? Register.PC = some (0x80006e98#64 : BitVec 64) := by
                  rw [obs_btaken_pc hobs21]; apply congrArg; apply BitVec.eq_of_toNat_eq; decide
                have ha0_21 := obs_btaken_other' hobs21 Register.x10 (by decide) ha0_20
                have ha2_21 := obs_btaken_other' hobs21 Register.x12 (by decide) ha2_20
                have hra_21 := obs_btaken_other' hobs21 Register.x1 (by decide) hra_20
                obtain ⟨vmi21, hmi21⟩ := obs_btaken_minstret hobs21
                have hmem21eq : σ21.mem = σ20.mem := hmem21
                have hloaded21 : StrcpyLoaded σ21.mem := by rw [hmem21eq]; exact hloaded20
                have hinv21 : MemInv dst src (len + 1) bs (8*p + 6 + 1) m0 σ21.mem := by
                  rw [hmem21eq]; exact hinv20
                have hframe21 : ∀ R, NotWrittenCpw R → σ21.regs.get? R = g R := fun R hR =>
                  (frame_btaken_cpw hobs21 R hR).trans (hframe20 R hR)
                have hsteps21 : Steps c ⟨σ21, i21, _⟩ := hsteps20.trans (Steps.single hs21)
                -- STEP e98: sb zero,7(a2) → store NUL byte 8p+7 = len at dst+len
                obtain ⟨sb7, shlo7, shhi7, shwin7⟩ :=
                  tail_sb_bounds dst src len p 7 (0x007#12) hreg hplo (by omega) sext_off7
                obtain ⟨σ22, i22, hs22, hi22, hG22, hmem22, hobs22⟩ :=
                  site_80006e98 σ21 i21 _ (0x80006e98#64) vmi21
                    (dst + BitVec.ofNat 64 (8*p)) hG21 hpc21 hmi21 ha2_21 hloaded21 rfl shlo7 shhi7 shwin7 hi21
                have hpc22 : σ22.regs.get? Register.PC = some (0x80006e9c#64 : BitVec 64) := by
                  have := obs_store_pc hobs22; rwa [show BitVec.addInt (0x80006e98#64) 4 = (0x80006e9c#64 : BitVec 64) from by decide] at this
                have ha0_22 := obs_store_other' hobs22 Register.x10 (by decide) ha0_21
                have hra_22 := obs_store_other' hobs22 Register.x1 (by decide) hra_21
                obtain ⟨vmi22, hmi22⟩ := obs_store_minstret hobs22
                have hloaded22 : StrcpyLoaded σ22.mem := by
                  rw [hmem22, mem_afterNextPC]
                  refine strcpy_loaded_insert σ21.mem _ _ ?_ hloaded21
                  have hcode := hreg.code_disjoint; rw [sb7]; omega
                -- the NUL store: stData 1 (0#64) = 0 = bs len; extends MemInv to len+1
                have hbsnul : bs (8*p + 7) = 0 := by rw [ht7]; exact hstrb.bs_nul
                have hinv22 : MemInv dst src (len + 1) bs (len + 1) m0 σ22.mem := by
                  rw [hmem22, mem_afterNextPC]
                  -- the site inserted `stData 1 (0#64)`; rewrite it to the meminv-store form
                  have hzeq : stData 1 (0#64) = stData 1 (zero_extend (m := 64) ((bs (8*p+7)) : BitVec (8*1))) := by
                    rw [hbsnul]
                    have : (zero_extend (m := 64) ((0 : BitVec 8) : BitVec (8*1))) = (0#64) := by
                      apply BitVec.eq_of_toNat_eq
                      simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]; decide
                    rw [this]
                  rw [hzeq]
                  have hinv21' : MemInv dst src (len + 1) bs (8*p + 7) m0 σ21.mem := by
                    have hcast : (8*p + 6 + 1) = 8*p + 7 := by omega
                    rw [hcast] at hinv21; exact hinv21
                  have hres := tail_meminv_store dst src len bs p 7 m0 σ21.mem hreg (by omega) sb7 hinv21'
                  have heq2 : 8*p + 7 + 1 = len + 1 := by omega
                  rw [heq2] at hres
                  exact hres
                obtain ⟨c', hsr, hpost⟩ := tail_ret g r dst src len m0 σ22.mem bs halign (0x80006e9c#64)
                  (Or.inr rfl) ⟨σ22, i22, _⟩
                  ⟨hG22, hloaded22, hpc22, ha0_22, hra_22, ⟨vmi22, hmi22⟩, hi22, hinv22,
                    fun R hR => (frame_store_cpw hobs22 R hR).trans (hframe21 R hR)⟩
                exact ⟨c', (hsteps21.trans (Steps.single hs22)).trans hsr, hpost⟩

/-! ## From the byte-tail entry `AtTailW` to the byte-tail postcondition

`AtTailW` is `∃p, 8p ≤ len < 8p+8 ∧ WTailCpw p`.  With `SrcWordMapped m0 src (len/8)` the
tail runs to `strcpy_word_bytepost`.  `p = len/8` is forced by `8p ≤ len < 8p+8`. -/
theorem tail_from_entry (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0) (hmap : SrcWordMapped m0 src (len / 8)) :
    Triple (AtTailW g r dst src len m0 bs) (strcpy_word_bytepost g r dst src len m0 bs) := by
  intro c hc
  obtain ⟨p, hplo, hphi, hTail⟩ := hc
  have hpeq : p = len / 8 := by omega
  subst hpeq
  exact wtail_to_done g r dst src len m0 bs (len / 8) halign hmap c hTail

/-! ## Aligned entry dispatch (`0x80006dc4 → 0x80006dd0`, aligned → word path)

* `0xdc4`: `or a5,a0,a1`;  `0xdc8`: `andi a5,a5,7`;  `0xdcc`: `bnez a5,0xe7c` NOT taken
  (`(dst|src)&7 = 0`, aligned) → fall through to the word-path entry `PreWord` (`0xdd0`). -/
structure PreWordEntry (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006dc4#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpwRegions dst src len
  strbytes : StrBytes m0 src len bs
  memeq : c.σ.mem = m0
  aligned : (dst.toNat ||| src.toNat) % 8 = 0
  hframe : ∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R

/-- Aligned entry dispatch `0xdc4 → 0xdd0`, establishing `PreWord` at the word path. -/
theorem entry_dispatch_word (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreWordEntry g r dst src len m0 bs) (PreWord g r dst src len m0 bs) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hreg, hstrb, hmemeq, halgn, hframe⟩ := hPre
  -- 0xdc4: or a5,a0,a1
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006dc4 c.σ c.tick c.steps (0x80006dc4#64) vmi dst src hgood hpc hmi ha0 ha1 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006dc8#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006dc4#64) 4 = (0x80006dc8#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- 0xdc8: andi a5,a5,7
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006dc8 σ1 i1 (c.steps + 1) (0x80006dc8#64) vmi1 (dst ||| src)
      hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006dcc#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006dc8#64) 4 = (0x80006dcc#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- 0xdcc: bnez a5 NOT taken (aligned)
  have hv : (((dst ||| src) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = false := by
    rw [andi7_ne_zero_iff]
    rw [BitVec.toNat_or] at *
    simp only [decide_eq_false_iff_not, Decidable.not_not]; exact halgn
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006dcc_nottaken σ2 i2 (c.steps + 1 + 1) (0x80006dcc#64) vmi2
      ((dst ||| src) &&& sign_extend (m := 64) (0x007#12))
      hG2 hpc2 hmi2' ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hv hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006dd0#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs3
    rwa [show BitVec.addInt (0x80006dcc#64) 4 = (0x80006dd0#64 : BitVec 64) from by decide] at this
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3), ?_⟩
  refine ⟨hG3, by rw [hmem3eq]; exact hloaded, hpc3,
    obs_bnottaken_other' hobs3 Register.x10 (by decide) ha0_2,
    obs_bnottaken_other' hobs3 Register.x11 (by decide) ha1_2,
    obs_bnottaken_other' hobs3 Register.x1 (by decide) hra_2,
    obs_bnottaken_minstret hobs3, hi3, hreg, hstrb, by rw [hmem3eq]; exact hmemeq, ?_⟩
  intro R hR
  have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_cpw hobs1 R hR.x15 hR
  have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_cpw hobs2 R hR.x15 hR
  have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_bnottaken_cpw hobs3 R hR
  rw [e3, e2, e1]; exact hframe R hR

/-! ## The aligned word-path total-correctness spec (`StrBytes`-phrased)

From the `strcpy` entry `0x80006dc4`, aligned (`(dst|src)%8 = 0`), the machine runs to
`r` with `x10 = dst` and the `len` chars + NUL copied into `[dst,dst+len]`.  Requires
`SrcWordMapped m0 src (len/8)` — the final aligned source word is fully mapped (the
`lbu` over-reads within the 8-aligned word, safe because the loop's `ld` already read
it). -/
theorem strcpy_word_bytespec (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0) (hmap : SrcWordMapped m0 src (len / 8)) :
    Triple (PreWordEntry g r dst src len m0 bs) (strcpy_word_bytepost g r dst src len m0 bs) :=
  ((entry_dispatch_word g r dst src len m0 bs).seq
    (entry_to_tail g r dst src len m0 bs)).seq
    (tail_from_entry g r dst src len m0 bs halign hmap)

/-! ## `CString`-phrased word spec (`strcpy_word_spec`)

Same `Q` shape as `StrcpySpec.strcpy_post` (PC = r, x10 = dst, x1 = r, chars + NUL copied,
outside unchanged, GoodState, tick < 2, blanket frame) — but with the aligned-path frame
`NotWrittenCpw` (the word path clobbers `x11…x16`, a strict superset of the byte-head
path's `x11/x14/x15`). -/
structure StrcpyWordPre (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006dc4#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpwRegions dst src s.length
  cstring : CString m0 src.toNat s
  memeq : c.σ.mem = m0
  aligned : (dst.toNat ||| src.toNat) % 8 = 0
  srcword : SrcWordMapped m0 src (s.length / 8)
  hframe : ∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R

/-- `CString`-phrased postcondition (same shape as `StrcpySpec.strcpy_post`, aligned
frame). -/
def strcpy_word_post (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ bs : Nat → BitVec 8,
    (∀ k, k ≤ s.length → m0[(src.toNat + k)]? = some (bs k)) ∧
    (∀ k, k ≤ s.length → c.σ.mem[(dst.toNat + k)]? = some (bs k))) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + s.length < a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R)

/-- **Top-level aligned `strcpy` word-path spec, `CString`-phrased.** -/
theorem strcpy_word_spec (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (halign : r.toNat % 4 = 0) :
    Triple (StrcpyWordPre g r dst src s m0) (strcpy_word_post g r dst src s m0) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, hra, hmi, htick, hreg, hcstr, hmemeq, halgn, hmap, hframe⟩ := hPre
  obtain ⟨len, bs, hlen, hstrb⟩ := cstring_bytes m0 src s hcstr
  subst hlen
  obtain ⟨c', hsteps, hpost⟩ :=
    strcpy_word_bytespec g r dst src s.length m0 bs halign hmap c
      ⟨hgood, hloaded, hpc, ha0, ha1, hra, hmi, htick, hreg, hstrb, hmemeq, halgn, hframe⟩
  obtain ⟨hG', hpc', ha0', hra', hcopied, houtside, htick', hframe'⟩ := hpost
  refine ⟨c', hsteps, hG', hpc', ha0', hra', ⟨bs, ?_, hcopied⟩, houtside, htick', hframe'⟩
  intro k hk
  exact strbytes_byte m0 src s.length bs hstrb k hk

/-! ## Top-level `strcpy` full spec (`strcpy_full_spec`)

`Triple.cases` over the `0xdcc` alignment test unifies the misaligned byte-head path
(`strcpy_spec`) and the aligned word path (`strcpy_word_spec`).  The shared precondition
`StrcpyFullPre` carries BOTH region witnesses (`CpyRegions` for the byte-head footprint,
`CpwRegions` for the word footprint) and the source-word mapping (used only on the
aligned branch), but NOT the alignment guard — the machine decides it.  The shared
postcondition uses the weaker aligned-path frame `NotWrittenCpw` (both paths' frames
weaken into it, since `NotWrittenCpw R → NotWrittenCpy R`). -/

/-- `NotWrittenCpw R → NotWrittenCpy R` (the word write-set `{x11..x16}` is a superset of
the byte-head write-set `{x11,x14,x15}`, so `NotWrittenCpw` is the stronger premise). -/
theorem notWrittenCpw_imp_cpy {R : Register} (h : NotWrittenCpw R) : NotWrittenCpy R :=
  ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2⟩

structure StrcpyFullPre (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006dc4#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  cregions : CpyRegions dst src s.length
  wregions : CpwRegions dst src s.length
  cstring : CString m0 src.toNat s
  memeq : c.σ.mem = m0
  srcword : SrcWordMapped m0 src (s.length / 8)
  hframe : ∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R

/-- Shared postcondition (aligned frame; both paths weaken into it). -/
def strcpy_full_post (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ bs : Nat → BitVec 8,
    (∀ k, k ≤ s.length → m0[(src.toNat + k)]? = some (bs k)) ∧
    (∀ k, k ≤ s.length → c.σ.mem[(dst.toNat + k)]? = some (bs k))) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + s.length < a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R)

/-- **Top-level `strcpy` full spec** — the machine copies `s` (chars + NUL) into
`[dst, dst+s.length]` regardless of alignment, `CString`-phrased. -/
theorem strcpy_full_spec (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (halign : r.toNat % 4 = 0) :
    Triple (StrcpyFullPre g r dst src s m0) (strcpy_full_post g r dst src s m0) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, hra, hmi, htick, hcreg, hwreg, hcstr, hmemeq, hmap, hframe⟩ := hPre
  by_cases halgn : (dst.toNat ||| src.toNat) % 8 = 0
  · -- aligned → word path (weaken the `NotWrittenCpy` g-frame to `NotWrittenCpw`)
    obtain ⟨c', hsteps, hpost⟩ :=
      strcpy_word_spec g r dst src s m0 halign c
        ⟨hgood, hloaded, hpc, ha0, ha1, hra, hmi, htick, hwreg, hcstr, hmemeq, halgn, hmap,
         fun R hR => hframe R (notWrittenCpw_imp_cpy hR)⟩
    obtain ⟨hG', hpc', ha0', hra', hcopy, hout, htick', hframe'⟩ := hpost
    exact ⟨c', hsteps, hG', hpc', ha0', hra', hcopy, hout, htick', hframe'⟩
  · -- misaligned → byte-head path
    obtain ⟨c', hsteps, hpost⟩ :=
      strcpy_spec g r dst src s m0 halign c
        ⟨hgood, hloaded, hpc, ha0, ha1, hra, hmi, htick, hcreg, hcstr, hmemeq, halgn, hframe⟩
    obtain ⟨hG', hpc', ha0', hra', hcopy, hout, htick', hframe'⟩ := hpost
    refine ⟨c', hsteps, hG', hpc', ha0', hra', hcopy, hout, htick',
      fun R hR => hframe' R (notWrittenCpw_imp_cpy hR)⟩

end Vsa.Sim

import Vsa.Sim.SnprintfSpec21
import Vsa.Sim.SnprintfSitesRet3
import Vsa.Sim.SnprintfSitesRet4
import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.CodeRangeInsert

/-!
# M3 Layer-3 — `SnprintfSpec22` : flush return, segment B
## `0x80007720` (parse-loop head) → `0x80007960` (NUL exit)

The parse loop re-reads the format cursor — which now points at the
terminating NUL of `"%lld"` — and exits through the `mbtowc = 0` arm:

```
  80007720: ld   s6,0(sp)          s6 := fmt cursor (→ NUL)
  80007724: ld   s4,232(s1)        s4 := __global_locale.mbtowc = __ascii_mbtowc
  80007728: jal  80010234          call __locale_mb_cur_max
    80010234: lbu a0,1000(gp)        a0 := __mb_cur_max = 1
    80010238: ret
  8000772c: mv   a3,a0             n := 1
  80007730: addi a4,sp,200         state buffer
  80007734: mv   a2,s6             s := cursor
  80007738: addi a1,sp,180         pwc := sp+180
  8000773c: mv   a0,s0             reent
  80007740: jalr s4                call __ascii_mbtowc  (indirect!)
    80012268: beqz a1,…              NOT taken (pwc ≠ 0)
    8001226c: beqz a2,…              NOT taken (s ≠ 0)
    80012270: beqz a3,…              NOT taken (n = 1 ≠ 0)
    80012274: lbu  a5,0(a2)          a5 := *cursor = 0  (the NUL)
    80012278: sw   a5,0(a1)          *pwc := 0
    8001227c: lbu  a0,0(a2)          a0 := 0
    80012280: snez a0,a0             a0 := 0
    80012284: ret
  80007744: beqz a0,80007960       TAKEN → the NUL exit
```

`retB_spec`: one `Steps` chain over the 20 sites (incl. both callee bodies —
inlined, not composed: they are 2 and 8 instructions).  Memory changes only by
the `sw` (`writeMap4` at `sp+180`).  Locale data facts (`mbtowc` pointer at
`0x8001b880`, `__mb_cur_max` byte at `0x8001b8f8`, `gp = 0x8001b510`,
`s1 = 0x8001b798`) are caller obligations — link-time constants of the binary,
dischargeable from the ELF image at the top level.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded __locale_mb_cur_maxLoaded
  __ascii_mbtowcLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Local pin-list surgery + value/guard helpers -/

theorem pins_drop3_rt {σ : MState} {a b c : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: L)) : PinsHold σ (a :: b :: L) :=
  ⟨h.1, h.2.1, h.2.2.2⟩

theorem pins_drop4_rt {σ : MState} {a b c d : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: L)) : PinsHold σ (a :: b :: c :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem pins_drop5_rt {σ : MState} {a b c d e : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: L)) : PinsHold σ (a :: b :: c :: d :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem beq64_false_of_toNat_ne_rt (a b : BitVec 64) (h : a.toNat ≠ b.toNat) :
    (a == b) = false := by
  rw [beq_eq_false_iff_ne]
  intro he; exact h (by rw [he])

theorem zext8_one_rt : (zero_extend (m := 64) (0x01#8) : BitVec 64) = 0x1#64 := by
  apply BitVec.eq_of_toNat_eq; decide

theorem zext8_zero_rt : (zero_extend (m := 64) (0x00#8) : BitVec 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- `snez` of zero is zero. -/
theorem snez_zero_rt :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (0#64))) : BitVec 64) = 0#64 := by
  have hz : zopz0zI_u (0#64) (0#64) = false := by
    simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]; decide
  rw [hz]; apply BitVec.eq_of_toNat_eq; decide

/-! ## Helper-code `Loaded` survival across the `sw` -/

theorem getElem?_insert_above_rt (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80014000 ≤ k) (a : Nat) (ha : a < 0x80014000) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- `__ascii_mbtowcLoaded` (code at `[0x80012268, 0x800122d0)`) survives a byte
store at/above `0x80014000`. -/
theorem amb_insert_rt (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80014000 ≤ k) (h : __ascii_mbtowcLoaded mem) :
    __ascii_mbtowcLoaded (mem.insert k v) := by
  unfold Vsa.Sim.Code.__ascii_mbtowcLoaded at h ⊢
  simp only [Vsa.Sim.Code.__ascii_mbtowcChunk0, Vsa.Sim.Code.__ascii_mbtowcChunk1] at h ⊢
  simp (disch := omega) only [getElem?_insert_above_rt mem k v hk]
  exact h

theorem amb_writeMap4_rt (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4))
    (ha : 0x80014000 ≤ a) (h : __ascii_mbtowcLoaded mem) :
    __ascii_mbtowcLoaded (writeMap4 mem a d) :=
  amb_insert_rt _ _ _ (by omega) (amb_insert_rt _ _ _ (by omega)
    (amb_insert_rt _ _ _ (by omega) (amb_insert_rt _ _ _ (by omega) h)))

/-! ## The segment theorem -/

/-- **Segment B of the flush return**: `0x80007720 → 0x80007960`.

Entry: parse-loop head after the flush cleanup (`retA_spec`'s exit).  The
format cursor slot `mem[sp]` holds `vcur` with `mem[vcur] = 0` (the
terminating NUL).  Exit: the `mbtowc = 0` NUL-exit arm at `0x80007960`, with
`s6 = vcur`, `a0 = 0`, and `mem32[sp+180]` zeroed (the wide-char out
parameter). -/
theorem retB_spec (vsp vcur v8 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hloc : __locale_mb_cur_maxLoaded c.σ.mem)
    (hamb : __ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007720#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx9 : c.σ.regs.get? Register.x9 = some (0x8001b798#64))
    (hslot0 : SlotHolds vsp 0x000 vcur c.σ.mem)
    (hfnslot : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) c.σ.mem)
    (hmb : c.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8))
    (hnul : c.σ.mem[vcur.toNat]? = some (0x00#8))
    (hcurlo : 0x80000000 ≤ vcur.toNat)
    (hcurhi : vcur.toNat + 1 ≤ 0x100000000)
    (hcurhtif : vcur.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vcur.toNat)
    (hcurdis : vcur.toNat + 1 ≤ vsp.toNat + 180 ∨ vsp.toNat + 184 ≤ vcur.toNat)
    (hsplo : 0x8001b900 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007960#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x22 = some vcur ∧
      c'.σ.regs.get? Register.x10 = some (0#64) ∧
      c'.σ.mem = writeMap4 c.σ.mem (vsp.toNat + 180) (swData (0#64)) ∧
      SvfprintfSliceLoaded c'.σ.mem ∧ FlushPinsLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hnw : vsp.toNat + 592 < 2 ^ 64 := by omega
  have hoff0 : (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
    rw [sext0_add_rt vsp]
  have hoffloc : ((0x8001b798#64 : BitVec 64) + sign_extend (m := 64) (0x0e8#12)).toNat
      = 0x8001b880 := by decide
  have hoffgp : ((0x8001b510#64 : BitVec 64) + sign_extend (m := 64) (0x3e8#12)).toNat
      = 0x8001b8f8 := by decide
  have hoffcur : (vcur + sign_extend (m := 64) (0x000#12)).toNat = vcur.toNat := by
    rw [sext0_add_rt vcur]
  have hoff180 : ((vsp + sign_extend (m := 64) (0x0b4#12)) + sign_extend (m := 64)
      (0x000#12)).toNat = vsp.toNat + 180 := by
    rw [sext0_add_rt, ptr_addoff vsp _ 180 (by decide) (by omega)]
  -- pin bundle L0: [x2, x3, x8, x9]
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, (0x8001b510#64 : BitVec 64)⟩,
      ⟨Register.x8, v8⟩, ⟨Register.x9, (0x8001b798#64 : BitVec 64)⟩] :=
    ⟨hx2, hx3, hx8, hx9, trivial⟩
  -- === 7720: ld s6,0(sp)  (s6 := fmt cursor = vcur) ===
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := slot_reload_bytes vsp 0x000 vcur c.σ.mem hslot0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80007720_rt c.σ c.tick c.steps _ vmi0 vsp _ _ _ _ _ _ _ _
      hG hpc hmi0 hp0.1 hload rfl
      (by rw [hoff0]; omega) (by rw [hoff0]; omega) (Or.inr (by rw [hoff0, htoh]; omega))
      (by rw [hoff0]; omega) ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007724#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80007720#64) 4 = (0x80007724#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx22_1 : σ1.regs.get? Register.x22 = some vcur := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vcur] at this
  -- L1: [x22, x2, x3, x8, x9]
  have hp1 := pins_cons_rt hx22_1 (pins_alu hobs1 (by rfl) hp0)
  have hmE1 : σ1.mem = c.σ.mem := hmem1
  -- === 7724: ld s4,232(s1)  (s4 := __ascii_mbtowc fn ptr) ===
  have hfn1 : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) σ1.mem := by
    rw [hmE1]; exact hfnslot
  obtain ⟨hb0, hb1', hb2', hb3', hb4, hb5, hb6, hb7⟩ :=
    slot_reload_bytes (0x8001b798#64) 0x0e8 (0x80012268#64) σ1.mem hfn1
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80007724_rt σ1 i1 (c.steps + 1) _ vmi1 (0x8001b798#64) _ _ _ _ _ _ _ _
      hG1 hpc1 hmi1 hp1.2.2.2.2.1 (hmE1 ▸ hload) rfl
      (by rw [hoffloc]; omega) (by rw [hoffloc]; omega) (Or.inr (by rw [hoffloc, htoh]; omega))
      (by rw [hoffloc]) hb0 hb1' hb2' hb3' hb4 hb5 hb6 hb7 hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007728#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80007724#64) 4 = (0x80007728#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx20_2 : σ2.regs.get? Register.x20 = some (0x80012268#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble (0x80012268#64)] at this
  -- L2: [x20, x22, x2, x3, x8, x9]
  have hp2 := pins_cons_rt hx20_2 (pins_alu hobs2 (by rfl) hp1)
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1
  -- === 7728: jal ra,__locale_mb_cur_max ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80007728_rt σ2 i2 (c.steps + 1 + 1) _ vmi2
      hG2 hpc2 hmi2 (hmE2 ▸ hload) rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80010234#64) := by
    have := obs_jal_pc hobs3
    rwa [show (0x80007728#64 : BitVec 64) + sign_extend (m := 64) (0x008b0c#21)
      = (0x80010234#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_jal_minstret hobs3
  have hx1_3 : σ3.regs.get? Register.x1 = some (0x8000772c#64) := by
    have := obs_jal_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80007728#64) 4 = (0x8000772c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  -- L3: [x1, x20, x22, x2, x3, x8, x9]
  have hp3 := pins_cons_rt hx1_3 (pins_jal hobs3 (by rfl) hp2)
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2
  -- === 10234: lbu a0,1000(gp)  (a0 := __mb_cur_max = 1) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80010234_rt3 σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 (0x8001b510#64) (0x01#8)
      hG3 hpc3 hmi3 hp3.2.2.2.2.1 (hmE3 ▸ hloc) rfl
      (by rw [hoffgp]; omega) (by rw [hoffgp]; omega) (Or.inr (by rw [hoffgp, htoh]; omega))
      (by rw [hoffgp, hmE3]; exact hmb) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80010238#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80010234#64) 4 = (0x80010238#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hx10_4 : σ4.regs.get? Register.x10 = some (0x1#64) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [zext8_one_rt] at this
  -- L4: [x10, x1, x20, x22, x2, x3, x8, x9]
  have hp4 := pins_cons_rt hx10_4 (pins_alu hobs4 (by rfl) hp3)
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3
  -- === 10238: ret  (back to 0x8000772c) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80010238_rt3 σ4 i4 (c.steps + 1 + 1 + 1 + 1) _ vmi4 (0x8000772c#64)
      hG4 hpc4 hmi4 hp4.2.1 (hmE4 ▸ hloc) rfl
      (by rw [ret_tgt _ (by decide)]; decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩
      ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000772c#64) := by
    have := obs_jr_pc hobs5
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi5, hmi5⟩ := obs_jr_minstret hobs5
  have hp5 := pins_jr hobs5 (by rfl) hp4
  have hmE5 : σ5.mem = c.σ.mem := hmem5.trans hmE4
  -- === 772c: mv a3,a0  (n := 1) ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_8000772c_rt σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) _ vmi5 (0x1#64)
      hG5 hpc5 hmi5 hp5.1 (hmE5 ▸ hload) rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007730#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x8000772c#64) 4 = (0x80007730#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hx13_6 : σ6.regs.get? Register.x13 = some (0x1#64) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_rt (0x1#64)] at this
  -- L6: [x13, x10, x1, x20, x22, x2, x3, x8, x9]
  have hp6 := pins_cons_rt hx13_6 (pins_alu hobs6 (by rfl) hp5)
  have hmE6 : σ6.mem = c.σ.mem := hmem6.trans hmE5
  -- === 7730: addi a4,sp,200  (mbstate buffer; value untracked) ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80007730_rt σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) _ vmi6 vsp
      hG6 hpc6 hmi6 hp6.2.2.2.2.2.1 (hmE6 ▸ hload) rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007734#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80007730#64) 4 = (0x80007734#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hp7 := pins_alu hobs7 (by rfl) hp6
  have hmE7 : σ7.mem = c.σ.mem := hmem7.trans hmE6
  -- === 7734: mv a2,s6  (s := vcur) ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80007734_rt σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi7 vcur
      hG7 hpc7 hmi7 hp7.2.2.2.2.1 (hmE7 ▸ hload) rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80007738#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80007734#64) 4 = (0x80007738#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hx12_8 : σ8.regs.get? Register.x12 = some vcur := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_rt vcur] at this
  -- L8: [x12, x13, x10, x1, x20, x22, x2, x3, x8, x9]
  have hp8 := pins_cons_rt hx12_8 (pins_alu hobs8 (by rfl) hp7)
  have hmE8 : σ8.mem = c.σ.mem := hmem8.trans hmE7
  -- === 7738: addi a1,sp,180  (pwc) ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80007738_rt σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi8 vsp
      hG8 hpc8 hmi8 hp8.2.2.2.2.2.2.1 (hmE8 ▸ hload) rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000773c#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80007738#64) 4 = (0x8000773c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hx11_9 : σ9.regs.get? Register.x11
      = some (vsp + sign_extend (m := 64) (0x0b4#12)) :=
    obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
  -- L9: [x11, x12, x13, x10, x1, x20, x22, x2, x3, x8, x9]
  have hp9 := pins_cons_rt hx11_9 (pins_alu hobs9 (by rfl) hp8)
  have hmE9 : σ9.mem = c.σ.mem := hmem9.trans hmE8
  -- === 773c: mv a0,s0  (reent) ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_8000773c_rt σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi9 v8
      hG9 hpc9 hmi9 hp9.2.2.2.2.2.2.2.2.2.1 (hmE9 ▸ hload) rfl hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80007740#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x8000773c#64) 4 = (0x80007740#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hx10_10 : σ10.regs.get? Register.x10 = some v8 := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_rt v8] at this
  -- L10: [x10, x11, x12, x13, x1, x20, x22, x2, x3, x8, x9]
  have hp10 := pins_cons_rt hx10_10 (pins_alu hobs10 (by rfl) (pins_drop4_rt hp9))
  have hmE10 : σ10.mem = c.σ.mem := hmem10.trans hmE9
  -- === 7740: jalr ra,0(s4)  →  __ascii_mbtowc (0x80012268), ra := 0x80007744 ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80007740_rt5 σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi10
      (0x80012268#64)
      hG10 hpc10 hmi10 hp10.2.2.2.2.2.1 (hmE10 ▸ hload) rfl
      (by rw [ret_tgt _ (by decide)]; decide) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80012268#64) := by
    have := obs_jalr_pc hobs11
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi11, hmi11⟩ := obs_jalr_minstret hobs11
  have hx1_11 : σ11.regs.get? Register.x1 = some (0x80007744#64) := by
    have := obs_jalr_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80007740#64) 4 = (0x80007744#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  -- L11: [x1, x10, x11, x12, x13, x20, x22, x2, x3, x8, x9]
  have hp11 := pins_cons_rt hx1_11 (pins_jalr hobs11 (by rfl) (pins_drop5_rt hp10))
  have hmE11 : σ11.mem = c.σ.mem := hmem11.trans hmE10
  -- === 12268: beqz a1 NOT taken (pwc = sp+180 ≠ 0) ===
  have hgv12 : ((vsp + sign_extend (m := 64) (0x0b4#12)) == (0#64 : BitVec 64)) = false :=
    beq64_false_of_toNat_ne_rt _ _ (by
      rw [ptr_addoff vsp _ 180 (by decide) (by omega)]
      simp only [BitVec.toNat_ofNat]; omega)
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80012268_nottaken_rt4 σ11 i11 (c.steps + 11) _ vmi11 _
      hG11 hpc11 hmi11 hp11.2.2.1 (hmE11 ▸ hamb) rfl hgv12 hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 11 + 1⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x8001226c#64) := by
    have := obs_bnottaken_pc hobs12
    rwa [show BitVec.addInt (0x80012268#64) 4 = (0x8001226c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_bnottaken_minstret hobs12
  have hp12 := pins_bnottaken hobs12 (by rfl) hp11
  have hmE12 : σ12.mem = c.σ.mem := hmem12.trans hmE11
  -- === 1226c: beqz a2 NOT taken (cursor ≠ 0) ===
  have hgv13 : (vcur == (0#64 : BitVec 64)) = false :=
    beq64_false_of_toNat_ne_rt _ _ (by simp only [BitVec.toNat_ofNat]; omega)
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_8001226c_nottaken_rt4 σ12 i12 (c.steps + 11 + 1) _ vmi12 vcur
      hG12 hpc12 hmi12 hp12.2.2.2.1 (hmE12 ▸ hamb) rfl hgv13 hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 11 + 1⟩ ⟨σ13, i13, c.steps + 11 + 1 + 1⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80012270#64) := by
    have := obs_bnottaken_pc hobs13
    rwa [show BitVec.addInt (0x8001226c#64) 4 = (0x80012270#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_bnottaken_minstret hobs13
  have hp13 := pins_bnottaken hobs13 (by rfl) hp12
  have hmE13 : σ13.mem = c.σ.mem := hmem13.trans hmE12
  -- === 12270: beqz a3 NOT taken (n = 1) ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80012270_nottaken_rt4 σ13 i13 (c.steps + 11 + 1 + 1) _ vmi13 (0x1#64)
      hG13 hpc13 hmi13 hp13.2.2.2.2.1 (hmE13 ▸ hamb) rfl (by decide) hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 11 + 1 + 1⟩
      ⟨σ14, i14, c.steps + 11 + 1 + 1 + 1⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80012274#64) := by
    have := obs_bnottaken_pc hobs14
    rwa [show BitVec.addInt (0x80012270#64) 4 = (0x80012274#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_bnottaken_minstret hobs14
  have hp14 := pins_bnottaken hobs14 (by rfl) hp13
  have hmE14 : σ14.mem = c.σ.mem := hmem14.trans hmE13
  -- === 12274: lbu a5,0(a2)  (a5 := the NUL = 0) ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80012274_rt4 σ14 i14 (c.steps + 11 + 1 + 1 + 1) _ vmi14 vcur (0x00#8)
      hG14 hpc14 hmi14 hp14.2.2.2.1 (hmE14 ▸ hamb) rfl
      (by rw [hoffcur]; omega) (by rw [hoffcur]; omega)
      (by rw [hoffcur]; exact hcurhtif)
      (by rw [hoffcur, hmE14]; exact hnul) hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 11 + 1 + 1 + 1⟩
      ⟨σ15, i15, c.steps + 11 + 1 + 1 + 1 + 1⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80012278#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80012274#64) 4 = (0x80012278#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hx15_15 : σ15.regs.get? Register.x15 = some (0#64) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [zext8_zero_rt] at this
  -- L15: [x15, x1, x10, x11, x12, x13, x20, x22, x2, x3, x8, x9]
  have hp15 := pins_cons_rt hx15_15 (pins_alu hobs15 (by rfl) hp14)
  have hmE15 : σ15.mem = c.σ.mem := hmem15.trans hmE14
  -- === 12278: sw a5,0(a1)  (*pwc := 0) ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80012278_rt4 σ15 i15 (c.steps + 11 + 1 + 1 + 1 + 1) _ vmi15 _ (0#64)
      hG15 hpc15 hmi15 hp15.2.2.2.1 hp15.1 (hmE15 ▸ hamb) rfl
      (by rw [hoff180]; omega) (by rw [hoff180]; omega) (by rw [hoff180, htoh]; omega)
      (by rw [hoff180]; omega) hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 11 + 1 + 1 + 1 + 1⟩
      ⟨σ16, i16, c.steps + 11 + 1 + 1 + 1 + 1 + 1⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x8001227c#64) := by
    have := obs_store_pc hobs16
    rwa [show BitVec.addInt (0x80012278#64) 4 = (0x8001227c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_store_minstret hobs16
  have hp16 := pins_store hobs16 (by rfl) hp15
  have hm16 : σ16.mem = writeMap4 c.σ.mem (vsp.toNat + 180) (swData (0#64)) := by
    rw [hmem16, mem_afterNextPC, hmE15, hoff180]
  have hamb16 : __ascii_mbtowcLoaded σ16.mem := by
    rw [hm16]; exact amb_writeMap4_rt _ _ _ (by omega) hamb
  -- === 1227c: lbu a0,0(a2)  (a0 := 0; NUL byte survives the disjoint sw) ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_8001227c_rt4 σ16 i16 (c.steps + 11 + 1 + 1 + 1 + 1 + 1) _ vmi16 vcur (0x00#8)
      hG16 hpc16 hmi16 hp16.2.2.2.2.1 hamb16 rfl
      (by rw [hoffcur]; omega) (by rw [hoffcur]; omega)
      (by rw [hoffcur]; exact hcurhtif)
      (by rw [hoffcur, hm16]
          exact (getElem?_writeMap4_outside vcur.toNat (vcur.toNat + 1) c.σ.mem
            (vsp.toNat + 180) (swData (0#64)) (by omega) vcur.toNat (by omega)
            (by omega)).trans hnul) hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 11 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ17, i17, c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80012280#64) := by
    have := obs_alu_pc hobs17
    rwa [show BitVec.addInt (0x8001227c#64) 4 = (0x80012280#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  have hx10_17 : σ17.regs.get? Register.x10 = some (0#64) := by
    have := obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [zext8_zero_rt] at this
  -- L17: [x10, x15, x1, x11, x12, x13, x20, x22, x2, x3, x8, x9]
  have hp17 := pins_cons_rt hx10_17 (pins_alu hobs17 (by rfl) (pins_drop3_rt hp16))
  have hmE17 : σ17.mem = σ16.mem := hmem17
  -- === 12280: snez a0,a0  (a0 := 0) ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80012280_rt5 σ17 i17 (c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi17 (0#64)
      hG17 hpc17 hmi17 hp17.1 (hmE17 ▸ hamb16) rfl hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ18, i18, c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x80012284#64) := by
    have := obs_alu_pc hobs18
    rwa [show BitVec.addInt (0x80012280#64) 4 = (0x80012284#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  have hx10_18 : σ18.regs.get? Register.x10 = some (0#64) := by
    have := obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [snez_zero_rt] at this
  -- L18: [x10, x15, x1, x11, x12, x13, x20, x22, x2, x3, x8, x9]
  have hp18 := pins_cons_rt hx10_18 (pins_alu hobs18 (by rfl) hp17.2)
  have hmE18 : σ18.mem = σ16.mem := hmem18.trans hmE17
  -- === 12284: ret  (back to 0x80007744) ===
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_80012284_rt4 σ18 i18 (c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi18
      (0x80007744#64)
      hG18 hpc18 hmi18 hp18.2.2.1 (hmE18 ▸ hamb16) rfl
      (by rw [ret_tgt _ (by decide)]; decide) hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ19, i19, c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x80007744#64) := by
    have := obs_jr_pc hobs19
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi19, hmi19⟩ := obs_jr_minstret hobs19
  have hp19 := pins_jr hobs19 (by rfl) hp18
  have hmE19 : σ19.mem = σ16.mem := hmem19.trans hmE18
  have hload19 : SvfprintfSliceLoaded σ19.mem := by
    rw [hmE19, hm16]; exact svfprintfSlice_writeMap4_pe _ _ _ (by omega) hload
  -- === 7744: beqz a0 → 0x80007960 (TAKEN, mbtowc returned 0: the NUL) ===
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_80007744_taken_rt σ19 i19 (c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi19
      (0#64)
      hG19 hpc19 hmi19 hp19.1 hload19 rfl (by decide) hi19
  have hstep20 : Step ⟨σ19, i19, c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ20, i20, c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x80007960#64) := by
    have := obs_btaken_pc hobs20
    rwa [site_80007744_taken_rt_tgt] at this
  obtain ⟨vmi20, hmi20⟩ := obs_btaken_minstret hobs20
  have hp20 := pins_btaken hobs20 (by rfl) hp19
  have hm20 : σ20.mem = writeMap4 c.σ.mem (vsp.toNat + 180) (swData (0#64)) := by
    rw [hmem20, hmE19, hm16]
  have hload20 : SvfprintfSliceLoaded σ20.mem := hmem20 ▸ hload19
  have hfp20 : FlushPinsLoaded σ20.mem := by
    rw [hm20]; exact flushPins_writeMap4_pe _ _ _ (by omega) hfp
  refine ⟨⟨σ20, i20, c.steps + 11 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG20, hpc20,
    hp20.2.2.2.2.2.2.2.2.1, hp20.2.2.2.2.2.2.2.2.2.2.1, hp20.2.2.2.2.2.2.2.1, hp20.1,
    hm20, hload20, hfp20, hi20, ⟨vmi20, hmi20⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
    ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
    ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
    ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans
    ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans
    ((Steps.single hstep19).trans (Steps.single hstep20)))))))))))))))))))

end Vsa.Sim

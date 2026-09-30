import Vsa.Sim.StrcmpSpecCond
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.EnvGetSites2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Store Value)
open Vsa.Alloc
open Vsa.Sim.Code (Env_getLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem notWrittenStrcmp_of_abiPreserved (R : Register) (hR : AbiPreserved R = true) :
    NotWrittenStrcmp R := by
  cases R <;> simp_all [AbiPreserved, NotWrittenStrcmp]

structure ScanNames (mem : Mem) (pn : Nat) (name : BitVec 64) (nameStr : String)
    (f : Vsa.While.Frame) : Prop where
  maskPinned : MaskPinned mem
  nameCStr : CString mem name.toNat nameStr
  nameRegB : ∀ cs, CStr mem name.toNat cs → StrcmpRegion name cs.length
  nameRegW : ∀ cs, CStr mem name.toNat cs → StrcmpWSlack name cs.length
  bindPtr : ∀ i, (h : i < f.vars.length) → ∃ q, read64 mem (pn + 8 * i) = some q ∧
    CString mem q (f.vars[i].1)
  bindRegB : ∀ i, (h : i < f.vars.length) → ∀ q, read64 mem (pn + 8 * i) = some q →
    ∀ cs, CStr mem q cs → StrcmpRegion (BitVec.ofNat 64 q) cs.length
  bindRegW : ∀ i, (h : i < f.vars.length) → ∀ q, read64 mem (pn + 8 * i) = some q →
    ∀ cs, CStr mem q cs → StrcmpWSlack (BitVec.ofNat 64 q) cs.length

  slotLo : ∀ i, i < f.vars.length → 0x80000000 ≤ pn + 8 * i
  slotHi : ∀ i, i < f.vars.length → pn + 8 * i + 8 ≤ 0x100000000
  slotHtif : ∀ i, i < f.vars.length →
    pn + 8 * i + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ pn + 8 * i
  slotAlign : ∀ i, i < f.vars.length → (pn + 8 * i) % 8 = 0

structure ScanSt (g : (R : Register) → Option (RegisterType R))
    (pc env name out count pn r sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedG : Env_getLoaded c.σ.mem
  loadedS : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some pc

  env4 : c.σ.regs.get? Register.x20 = some env
  name3 : c.σ.regs.get? Register.x19 = some name
  out5 : c.σ.regs.get? Register.x21 = some out
  count2 : c.σ.regs.get? Register.x18 = some count
  cursor1 : c.σ.regs.get? Register.x9 = some (pn + BitVec.ofNat 64 (8 * i))
  idx0 : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i)
  ra : c.σ.regs.get? Register.x1 = some r
  sp2 : c.σ.regs.get? Register.x2 = some sp
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2

  frame : FrameRepr m0 N φf φc env.toNat f
  names : ScanNames m0 pn.toNat name nameStr f
  count_eq : count.toNat = f.vars.length
  ile : i ≤ f.vars.length
  ghost : ∀ R : Register, AbiPreserved R = true → c.σ.regs.get? R = g R

theorem sext64_id_eg4 (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d

theorem word8_recon_eg4 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
      : BitVec (8 * 8)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem read64_bytes_eg4 (mem : Mem) (a q : Nat) (h : read64 mem a = some q) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      mem[a]? = some b0 ∧ mem[a+1]? = some b1 ∧ mem[a+2]? = some b2 ∧
      mem[a+3]? = some b3 ∧ mem[a+4]? = some b4 ∧ mem[a+5]? = some b5 ∧
      mem[a+6]? = some b6 ∧ mem[a+7]? = some b7 ∧
      q = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [read64, readLE, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨b0, hb0, r1, ⟨b1, hb1, r2, ⟨b2, hb2, r3, ⟨b3, hb3, r4, ⟨b4, hb4, r5,
    ⟨b5, hb5, r6, ⟨b6, hb6, r7, ⟨b7, hb7, r8, hr8, hq7⟩, hq6⟩, hq5⟩, hq4⟩, hq3⟩,
    hq2⟩, hq1⟩, hq0⟩ := h
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hb1
  · simpa using hb2
  · simpa using hb3
  · simpa using hb4
  · simpa using hb5
  · simpa using hb6
  · simpa using hb7
  · subst hr8; simp only [Nat.add_zero, Nat.mul_zero] at *
    omega

theorem read64_lt_eg4 (mem : Mem) (a q : Nat) (h : read64 mem a = some q) : q < 2^64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hq⟩ := read64_bytes_eg4 mem a q h
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  omega

theorem ld_value_eq_read64 (mem : Mem) (a q : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : read64 mem a = some q)
    (e0 : mem[a]? = some b0) (e1 : mem[a+1]? = some b1) (e2 : mem[a+2]? = some b2)
    (e3 : mem[a+3]? = some b3) (e4 : mem[a+4]? = some b4) (e5 : mem[a+5]? = some b5)
    (e6 : mem[a+6]? = some b6) (e7 : mem[a+7]? = some b7) :
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 q := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, f0, f1, f2, f3, f4, f5, f6, f7, hq⟩ :=
    read64_bytes_eg4 mem a q h
  have hb0 : b0 = c0 := by rw [e0] at f0; injection f0
  have hb1 : b1 = c1 := by rw [e1] at f1; injection f1
  have hb2 : b2 = c2 := by rw [e2] at f2; injection f2
  have hb3 : b3 = c3 := by rw [e3] at f3; injection f3
  have hb4 : b4 = c4 := by rw [e4] at f4; injection f4
  have hb5 : b5 = c5 := by rw [e5] at f5; injection f5
  have hb6 : b6 = c6 := by rw [e6] at f6; injection f6
  have hb7 : b7 = c7 := by rw [e7] at f7; injection f7
  subst hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rw [sext64_id_eg4]
  apply BitVec.eq_of_toNat_eq
  rw [word8_recon_eg4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 mem a q h), ← hq]

theorem scan_c60_load (g : (R : Register) → Option (RegisterType R))
    (env name out count pn r sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) (q : Nat)
    (hSt : ScanSt g (0x80002c60#64) env name out count pn r sp i f nameStr N φf φc m0 c)
    (hilt : i < f.vars.length)
    (hq : read64 m0 (pn.toNat + 8 * i) = some q) :
    ∃ c', Step c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002c64#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 q) ∧
      c'.σ.regs.get? Register.x19 = some name ∧
      c'.σ.regs.get? Register.x1 = some r ∧
      c'.σ.mem = m0 ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
      (∃ v, c'.σ.regs.get? Register.minstret = some v) ∧
      c'.σ.sailOutput = c.σ.sailOutput ∧
      (∀ R : Register, AbiPreserved R = true → c'.σ.regs.get? R = g R) := by
  obtain ⟨vmi, hmi⟩ := hSt.minstret

  have hslotHi := hSt.names.slotHi i hilt
  have hslotLo := hSt.names.slotLo i hilt
  have hslotHt := hSt.names.slotHtif i hilt
  have hslotAl := hSt.names.slotAlign i hilt
  have hpnbnd : pn.toNat + 8 * i < 2^64 := by
    have := hslotHi; simp only [show (0x100000000 : Nat) = 2^32 from by decide] at this; omega
  have hcur : (pn + BitVec.ofNat 64 (8 * i)).toNat = pn.toNat + 8 * i :=
    ptrN pn (8 * i) (by omega)

  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, _⟩ :=
    read64_bytes_eg4 m0 (pn.toNat + 8 * i) q hq
  have hmem := hSt.mem

  have hsz : (pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12))
      = pn + BitVec.ofNat 64 (8 * i) := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]
  have hlo : 0x80000000 ≤ (pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat := by
    rw [hsz, hcur]; omega
  have hhiram : (pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 8
      ≤ 0x100000000 := by rw [hsz, hcur]; omega
  have hhtif : (pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat := by
    rw [hsz, hcur]; omega
  have halign : (pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0 := by
    rw [hsz, hcur]; omega

  have d0 : c.σ.mem[(pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat]?
      = some b0 := by rw [hsz, hmem, hcur]; exact e0
  have d1 : c.σ.mem[(pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 1]?
      = some b1 := by rw [hsz, hmem, hcur]; exact e1
  have d2 : c.σ.mem[(pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 2]?
      = some b2 := by rw [hsz, hmem, hcur]; exact e2
  have d3 : c.σ.mem[(pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 3]?
      = some b3 := by rw [hsz, hmem, hcur]; exact e3
  have d4 : c.σ.mem[(pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 4]?
      = some b4 := by rw [hsz, hmem, hcur]; exact e4
  have d5 : c.σ.mem[(pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 5]?
      = some b5 := by rw [hsz, hmem, hcur]; exact e5
  have d6 : c.σ.mem[(pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 6]?
      = some b6 := by rw [hsz, hmem, hcur]; exact e6
  have d7 : c.σ.mem[(pn + BitVec.ofNat 64 (8 * i) + sign_extend (m := 64) (0x000#12)).toNat + 7]?
      = some b7 := by rw [hsz, hmem, hcur]; exact e7
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80002c60_eg2 c.σ c.tick c.steps (0x80002c60#64) vmi (pn + BitVec.ofNat 64 (8 * i))
      b0 b1 b2 b3 b4 b5 b6 b7 hSt.good hSt.pc hmi hSt.cursor1 hSt.loadedG rfl
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7 hSt.tick

  have hval : (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 q :=
    ld_value_eq_read64 m0 (pn.toNat + 8 * i) q b0 b1 b2 b3 b4 b5 b6 b7 hq e0 e1 e2 e3 e4 e5 e6 e7

  have hpc' : σ'.regs.get? Register.PC = some (0x80002c64#64 : BitVec 64) := by
    have := obs_alu_pc hobs
    rwa [show BitVec.addInt (0x80002c60#64) 4 = (0x80002c64#64 : BitVec 64) from by decide] at this

  have hx10' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 q) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval] at this

  have hx19' := obs_alu_other hobs Register.x19 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hSt.name3

  have hra' := obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra

  obtain ⟨vmi', hmi'⟩ := obs_alu_minstret hobs
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hpc', hx10', hx19', hra',
    by rw [hmem']; exact hSt.mem, hG', hi', ⟨vmi', hmi'⟩,
    by rw [hobs.out, sailOutput_sigmaPost_alu], ?_⟩

  intro R hR
  have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
  have hrd : (Register.x10 == R) = false := hnws.2.2.2.1
  exact (sframe_alu hobs R hrd hnws).trans (hSt.ghost R hR)

end Vsa.Sim

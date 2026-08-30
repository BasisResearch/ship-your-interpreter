import Vsa.Sim.StrcmpSpecW
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcmp` word-path spec, part 2 (`strcmp_word_spec`, `strcmp_full_spec`)

Continues `StrcmpSpecW`: groups 1 and 2 of the 3×-unrolled word loop (offsets
`0x008`/`0x010`), the `Triple.loop` word-loop rule, the `slli/srli` lane compare
(`0xf20 … 0xf80`), the NUL-word exit blocks (`0xfac/0xfa4/0xfb8`), the aligned entry
(`0xea0 … 0xeb4`), and the top-level `strcmp_word_spec`/`strcmp_full_spec`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Shift-amount reductions

Each `slli`/`srli` in the lane compare uses `shift_bits_left/right v (extractLsb sh 5 0)`
where `sh ∈ {0x30, 0x20, 0x10}`. These reduce to `v <<< N` / `v >>> N` with
`N ∈ {48, 32, 16}` — the extracted 6-bit shamt is the literal shift. -/

theorem shl_48 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x30#6) 5 0) = v <<< (48:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x30#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x30#6) 5 0 : BitVec 6) = (48#6 : BitVec 6) from rfl]
  rfl

theorem shl_32 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x20#6) 5 0) = v <<< (32:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x20#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x20#6) 5 0 : BitVec 6) = (32#6 : BitVec 6) from rfl]
  rfl

theorem shl_16 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x10#6) 5 0) = v <<< (16:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x10#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x10#6) 5 0 : BitVec 6) = (16#6 : BitVec 6) from rfl]
  rfl

theorem shr_48 (v : BitVec 64) :
    shift_bits_right v (Sail.BitVec.extractLsb (0x30#6) 5 0) = v >>> (48:Nat) := by
  show v >>> (Sail.BitVec.extractLsb (0x30#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x30#6) 5 0 : BitVec 6) = (48#6 : BitVec 6) from rfl]
  rfl

/-! ## The `word_off` pointer lemma

Group 1/2 load at `(pa + 24j) + sext(8)` and `(pa + 24j) + sext(16)`. This equals
`pa + (24j + 8)` and `pa + (24j + 16)` as pointers. -/

/-- `(p + ofNat (24j)) + sext(8) = p + ofNat (24j + 8)`. -/
theorem word_off8 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x008#12)
      = p + BitVec.ofNat 64 (24*j + 8) := by
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `(p + ofNat (24j)) + sext(16) = p + ofNat (24j + 16)`. -/
theorem word_off16 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x010#12)
      = p + BitVec.ofNat 64 (24*j + 16) := by
  rw [show (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `(p + ofNat (24j)) + sext(24) = p + ofNat (24(j+1))` (group-2 back-edge). -/
theorem word_off24 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x018#12)
      = p + BitVec.ofNat 64 (24*(j+1)) := by
  rw [show (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 24*j + 24 = 24*(j+1) from by omega]

/-! ## Group entry states

`WHead1 j` (at `0xed8`) and `WHead2 j` (at `0xef8`) are the entry states of groups 1
and 2: identical register content to `WHead` (pointers `pa+24j`/`pb+24j`, `a5=magic7f`,
`t2=allOnes`), plus the group-`g` prefix invariant `BytePrefix csa csb (24j + 8g)` and
A-NUL-freedom `24j + 8g ≤ la` established by the previous group's continue. The bodies
load at offset `8g`, so `a2/a3` cover the word at `pa.toNat + 24j + 8g`. -/

/-- Group-1 entry at `0xed8` (offset `24j + 8`). -/
structure WHead1 (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some (0x80006ed8#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*j))
  a1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*j))
  a5 : c.σ.regs.get? Register.x15 = some magic7f
  t2 : c.σ.regs.get? Register.x7 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpWRegion pa csa.length
  regb : StrcmpWRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  maskpin : MaskPinned m0
  prefixEq : BytePrefix csa csb (24*j + 8)
  jle : 24*j + 8 ≤ csa.length
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- Group-2 entry at `0xef8` (offset `24j + 16`). -/
structure WHead2 (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some (0x80006ef8#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*j))
  a1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*j))
  a5 : c.σ.regs.get? Register.x15 = some magic7f
  t2 : c.σ.regs.get? Register.x7 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpWRegion pa csa.length
  regb : StrcmpWRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  maskpin : MaskPinned m0
  prefixEq : BytePrefix csa csb (24*j + 16)
  jle : 24*j + 16 ≤ csa.length
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- Group-`g` mid-state at the `bne t0,t2` PC `pc`, offset `n`. Uniform in the two
non-zero groups: `a2 = wa`, `a3 = wb`, `t0 = strlenWordVal wa`, `t2 = allOnes`,
pointers still at `pa+24j`. The prefix invariant is at offset `n`. -/
structure WGmid (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j n : Nat) (pc : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*j))
  a1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*j))
  a2 : c.σ.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + n))
  a3 : c.σ.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + n))
  a5 : c.σ.regs.get? Register.x15 = some magic7f
  t0 : c.σ.regs.get? Register.x5 = some (strlenWordVal (cwordAt m0 (pa.toNat + n)))
  t2 : c.σ.regs.get? Register.x7 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpWRegion pa csa.length
  regb : StrcmpWRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  maskpin : MaskPinned m0
  prefixEq : BytePrefix csa csb n
  jle : n ≤ csa.length
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- Group-1 straight-line `0xed8 → 0xef0`: `ld a2,8(a0)`; `ld a3,8(a1)`; four magic-ALU
ops. Produces `WGmid` at PC `0xef0`, offset `24j + 8`. -/
theorem wg1_straight (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WHead1 g pa pb r csa csb m0 o j)
      (WGmid g pa pb r csa csb m0 o j (24*j + 8) (0x80006ef0#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, ha5, ht2, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, hpre, hjle, hframe⟩ := hSt
  have hjleb : 24*j + 8 ≤ csb.length := prefix_le_lenb hpre
  -- load bounds at offset 24j+8 for A and B (n = 24j+8, n % 8 = 0)
  obtain ⟨htna, hloa, hhia, hhtifa, halgna⟩ := wcmp_load_bounds pa csa.length (24*j+8) hrega hjle (by omega)
  obtain ⟨htnb, hlob, hhib, hhtifb, halgnb⟩ := wcmp_load_bounds pb csb.length (24*j+8) hregb hjleb (by omega)
  rw [sext0_add] at hloa hhia hhtifa halgna hlob hhib hhtifb halgnb
  -- === ed8: ld a2,8(a0) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006ed8 c.σ c.tick c.steps (0x80006ed8#64) vmi (pa + BitVec.ofNat 64 (24*j))
      hgood hpc hmi ha0 hloaded rfl
      (by rw [word_off8]; exact hloa) (by rw [word_off8]; exact hhia)
      (by rw [word_off8]; exact hhtifa) (by rw [word_off8]; exact halgna) htick
  have hwordA : (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude c.σ) (0x80006ed8#64))
        (pa + BitVec.ofNat 64 (24*j) + sign_extend (m := 64) (0x008#12))))
      = cwordAt m0 (pa.toNat + (24*j + 8)) := by
    rw [word_off8, sext64_self, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem, htna]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006edc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006ed8#64) 4 = (0x80006edc#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha5_1 := obs_alu_other' hobs1 Register.x15 (by decide) ha5
  have ht2_1 := obs_alu_other' hobs1 Register.x7 (by decide) ht2
  have ha2_1 : σ1.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + (24*j+8))) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hwordA] at this
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === edc: ld a3,8(a1) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006edc σ1 i1 (c.steps + 1) (0x80006edc#64) vmi1 (pb + BitVec.ofNat 64 (24*j))
      hG1 hpc1 hmi1' ha1_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [word_off8]; exact hlob) (by rw [word_off8]; exact hhib)
      (by rw [word_off8]; exact hhtifb) (by rw [word_off8]; exact halgnb) hi1
  have hwordB : (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude σ1) (0x80006edc#64))
        (pb + BitVec.ofNat 64 (24*j) + sign_extend (m := 64) (0x008#12))))
      = cwordAt m0 (pb.toNat + (24*j + 8)) := by
    rw [word_off8, sext64_self, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem1, hmem, htnb]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006ee0#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006edc#64) 4 = (0x80006ee0#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have ha5_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha5_1
  have ht2_2 := obs_alu_other' hobs2 Register.x7 (by decide) ht2_1
  have ha3_2 : σ2.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + (24*j+8))) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hwordB] at this
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === ee0: and t0,a2,a5 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006ee0 σ2 i2 (c.steps + 1 + 1) (0x80006ee0#64) vmi2 (cwordAt m0 (pa.toNat + (24*j+8))) magic7f
      hG2 hpc2 hmi2' ha2_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006ee4#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006ee0#64) 4 = (0x80006ee4#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
  have ha3_3 := obs_alu_other' hobs3 Register.x13 (by decide) ha3_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have ht2_3 := obs_alu_other' hobs3 Register.x7 (by decide) ht2_2
  have ht0_3 : σ3.regs.get? Register.x5 = some (cwordAt m0 (pa.toNat + (24*j+8)) &&& magic7f) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.1 hR).trans (hframe_2 R hR)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === ee4: or t1,a2,a5 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006ee4 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006ee4#64) vmi3 (cwordAt m0 (pa.toNat + (24*j+8))) magic7f
      hG3 hpc3 hmi3' ha2_3 ha5_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006ee8#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006ee4#64) 4 = (0x80006ee8#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_alu_other' hobs4 Register.x11 (by decide) ha1_3
  have ha2_4 := obs_alu_other' hobs4 Register.x12 (by decide) ha2_3
  have ha3_4 := obs_alu_other' hobs4 Register.x13 (by decide) ha3_3
  have ha5_4 := obs_alu_other' hobs4 Register.x15 (by decide) ha5_3
  have ht2_4 := obs_alu_other' hobs4 Register.x7 (by decide) ht2_3
  have ht0_4 := obs_alu_other' hobs4 Register.x5 (by decide) ht0_3
  have ht1_4 : σ4.regs.get? Register.x6 = some (cwordAt m0 (pa.toNat + (24*j+8)) ||| magic7f) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs4 R hR.2.1 hR).trans (hframe_3 R hR)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === ee8: add t0,t0,a5 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006ee8 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006ee8#64) vmi4
      (cwordAt m0 (pa.toNat + (24*j+8)) &&& magic7f) magic7f
      hG4 hpc4 hmi4' ht0_4 ha5_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006eec#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006ee8#64) 4 = (0x80006eec#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ha2_5 := obs_alu_other' hobs5 Register.x12 (by decide) ha2_4
  have ha3_5 := obs_alu_other' hobs5 Register.x13 (by decide) ha3_4
  have ha5_5 := obs_alu_other' hobs5 Register.x15 (by decide) ha5_4
  have ht2_5 := obs_alu_other' hobs5 Register.x7 (by decide) ht2_4
  have ht1_5 := obs_alu_other' hobs5 Register.x6 (by decide) ht1_4
  have ht0_5 : σ5.regs.get? Register.x5 = some ((cwordAt m0 (pa.toNat + (24*j+8)) &&& magic7f) + magic7f) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs5 R hR.1 hR).trans (hframe_4 R hR)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === eec: or t0,t0,t1 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006eec σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006eec#64) vmi5
      ((cwordAt m0 (pa.toNat + (24*j+8)) &&& magic7f) + magic7f) (cwordAt m0 (pa.toNat + (24*j+8)) ||| magic7f)
      hG5 hpc5 hmi5' ht0_5 ht1_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006ef0#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006eec#64) 4 = (0x80006ef0#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_alu_other' hobs6 Register.x11 (by decide) ha1_5
  have ha2_6 := obs_alu_other' hobs6 Register.x12 (by decide) ha2_5
  have ha3_6 := obs_alu_other' hobs6 Register.x13 (by decide) ha3_5
  have ha5_6 := obs_alu_other' hobs6 Register.x15 (by decide) ha5_5
  have ht2_6 := obs_alu_other' hobs6 Register.x7 (by decide) ht2_5
  have ht0_6 : σ6.regs.get? Register.x5 = some (strlenWordVal (cwordAt m0 (pa.toNat + (24*j+8)))) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [strcmpWordVal_eq] at this
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have hframe_6 : ∀ R, NotWrittenStrcmp R → σ6.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs6 R hR.1 hR).trans (hframe_5 R hR)
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  have hmem6eq : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  have hout6 : σ6.sailOutput = o :=
    (by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5, hobs6] :
      σ6.sailOutput = c.σ.sailOutput).trans hout
  refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6), ?_⟩
  exact ⟨hG6, by rw [hmem6eq]; exact hloaded, by rw [hmem6eq]; exact hmem, hout6, hpc6, ha0_6, ha1_6,
    ha2_6, ha3_6, ha5_6, ht0_6, ht2_6, hra_6, ⟨vmi6, hmi6'⟩, hi6, hrega, hregb, hcstra, hcstrb,
    hmaskpin, hpre, hjle, hframe_6⟩

/-! ## The word-path exit disjunct (`WordExit`)

A group's three-way dispatch that does not continue lands in an EXIT: either the lane
compare `WLaneCmp` (words differ, A NUL-free) or a NUL-word block. We bundle both as
`WordExit`, a PC-tagged terminal the loop rule can drop the measure on. The lane arm
carries the full `WLaneCmp` state (offset `n`); the NUL arm (`WNulExit`, below) carries a
FULL register state — pointers `a0/a1 = pa/pb + 24j`, the cached words `a2/a3` at the NUL
offset `n = 24j + off(pc)`, `x1 = r`, `minstret`, `tick`, `GoodState`, `mem = m0`, the
`CStr`/`StrcmpWRegion` witnesses, `MaskPinned`, ghost frame — plus the byte-level
`n ≤ la < n+8` and `BytePrefix csa csb n` facts. Downstream (`StrcmpSpecW4`) the NUL-exit
blocks re-test `a2,a3` and either return `0` (equal) or run the byte loop at the advanced
pointer `pa+n` (differ), so ALL of those registers/witnesses are needed. -/

/-- Per-PC pointer-advance offset for the three NUL blocks: `fac` fires at the group-0
offset (`+0`), `fa4` at the group-1 offset (`+8`, adjusted by its `addi`s), `fb8` at the
group-2 offset (`+16`). -/
def nulOff (pc : BitVec 64) : Nat :=
  if pc = (0x80006fa4#64 : BitVec 64) then 8
  else if pc = (0x80006fb8#64 : BitVec 64) then 16
  else 0

/-- Widened NUL-exit state at a NUL block (`fac`/`fa4`/`fb8`), word iteration `j`, byte
offset `n = 24j + off(pc)`. A's word at `n` holds the NUL (`la < n+8`), the pointers are
`a0 = pa + 24j`, `a1 = pb + 24j` (NOT yet advanced by the block's `addi`s), the cached
words are `a2 = cwordAt (pa+n)`, `a3 = cwordAt (pb+n)`. Mirrors the lane arm / `WGmid` in
the register content it preserves. -/
structure WNulExit (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) (pc : BitVec 64) (c : Config) : Prop where
  pcv : pc = (0x80006fac#64 : BitVec 64) ∨ pc = (0x80006fa4#64 : BitVec 64)
      ∨ pc = (0x80006fb8#64 : BitVec 64)
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pcget : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*j))
  a1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*j))
  a2 : c.σ.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + (24*j + nulOff pc)))
  a3 : c.σ.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + (24*j + nulOff pc)))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpWRegion pa csa.length
  regb : StrcmpWRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  maskpin : MaskPinned m0
  prefixEq : BytePrefix csa csb (24*j + nulOff pc)
  hasnul : csa.length < 24*j + nulOff pc + 8
  jle : 24*j + nulOff pc ≤ csa.length
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- Loop exit: lane compare or a NUL block. The lane arm carries `WLaneCmp n`; the NUL arm
carries `WNulExit` (full register state at a NUL block). -/
def WordExit (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  (∃ n, WLaneCmp g pa pb r csa csb m0 o n c) ∨
  (∃ (j : Nat) (pc : BitVec 64), WNulExit g pa pb r csa csb m0 o j pc c)

/-- Group-1 three-way dispatch `0xef0 → {0xfa4, 0xf20, 0xef8}`. -/
theorem wg1_dispatch (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WGmid g pa pb r csa csb m0 o j (24*j + 8) (0x80006ef0#64))
      (fun c => WHead2 g pa pb r csa csb m0 o j c ∨ WordExit g pa pb r csa csb m0 o c) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, ha2, ha3, ha5, ht0, ht2, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, hpre, hjle, hframe⟩ := hSt
  by_cases hnul : strlenWordVal (cwordAt m0 (pa.toNat + (24*j+8))) = BitVec.allOnes 64
  · have hguard : ((strlenWordVal (cwordAt m0 (pa.toNat + (24*j+8)))) != (BitVec.allOnes 64)) = false := by rw [hnul]; simp
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006ef0_nottaken c.σ c.tick c.steps (0x80006ef0#64) vmi
        (strlenWordVal (cwordAt m0 (pa.toNat + (24*j+8)))) (BitVec.allOnes 64)
        hgood hpc hmi ht0 ht2 hloaded rfl hguard htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006ef4#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006ef0#64) 4 = (0x80006ef4#64 : BitVec 64) from by decide] at this
    have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_bnottaken_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_bnottaken_other' hobs1 Register.x12 (by decide) ha2
    have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
    have ha5_1 := obs_bnottaken_other' hobs1 Register.x15 (by decide) ha5
    have ht2_1 := obs_bnottaken_other' hobs1 Register.x7 (by decide) ht2
    have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
    have hnf : 24*j + 8 + 8 ≤ csa.length := by
      rcases Nat.lt_or_ge csa.length (24*j + 8 + 8) with hlt | hge
      · exact absurd hnul (word_has_nul m0 pa csa hcstra (24*j+8) hjle hlt)
      · exact hge
    by_cases hwordeq : cwordAt m0 (pa.toNat + (24*j+8)) = cwordAt m0 (pb.toNat + (24*j+8))
    · have hguard2 : ((cwordAt m0 (pa.toNat + (24*j+8))) != (cwordAt m0 (pb.toNat + (24*j+8)))) = false := by rw [hwordeq]; simp
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site_80006ef4_nottaken σ1 i1 (c.steps + 1) (0x80006ef4#64) vmi1
          (cwordAt m0 (pa.toNat + (24*j+8))) (cwordAt m0 (pb.toNat + (24*j+8)))
          hG1 hpc1 hmi1' ha2_1 ha3_1 (by rw [hmem1]; exact hloaded) rfl hguard2 hi1
      have hpc2 : σ2.regs.get? Register.PC = some (0x80006ef8#64 : BitVec 64) := by
        have := obs_bnottaken_pc hobs2; rwa [show BitVec.addInt (0x80006ef4#64) 4 = (0x80006ef8#64 : BitVec 64) from by decide] at this
      have ha0_2 := obs_bnottaken_other' hobs2 Register.x10 (by decide) ha0_1
      have ha1_2 := obs_bnottaken_other' hobs2 Register.x11 (by decide) ha1_1
      have ha5_2 := obs_bnottaken_other' hobs2 Register.x15 (by decide) ha5_1
      have ht2_2 := obs_bnottaken_other' hobs2 Register.x7 (by decide) ht2_1
      have hra_2 := obs_bnottaken_other' hobs2 Register.x1 (by decide) hra_1
      have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
        fun R hR => (sframe_bnottaken hobs2 R hR).trans (hframe_1 R hR)
      obtain ⟨vmi2, hmi2'⟩ := obs_bnottaken_minstret hobs2
      have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
      have hpre1 : BytePrefix csa csb (24*j + 8 + 8) :=
        byte_prefix_extend m0 pa pb csa csb hcstra hcstrb (24*j+8) hpre (prefix_le_lenb hpre) hwordeq hnf
      have hout2 : σ2.sailOutput = o :=
        (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
      refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), Or.inl ?_⟩
      exact ⟨hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hout2, hpc2,
        ha0_2, ha1_2, ha5_2, ht2_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hrega, hregb, hcstra, hcstrb,
        hmaskpin, (by rw [show 24*j + 16 = 24*j + 8 + 8 from by omega]; exact hpre1),
        (by rw [show 24*j + 16 = 24*j + 8 + 8 from by omega]; exact hnf), hframe_2⟩
    · have hguard2 : ((cwordAt m0 (pa.toNat + (24*j+8))) != (cwordAt m0 (pb.toNat + (24*j+8)))) = true := by rw [bne_iff_ne]; exact hwordeq
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site_80006ef4_taken σ1 i1 (c.steps + 1) (0x80006ef4#64) vmi1
          (cwordAt m0 (pa.toNat + (24*j+8))) (cwordAt m0 (pb.toNat + (24*j+8)))
          hG1 hpc1 hmi1' ha2_1 ha3_1 (by rw [hmem1]; exact hloaded) rfl hguard2 hi1
      have hpceq : (0x80006ef4#64 : BitVec 64) + sign_extend (m := 64) (0x002c#13) = (0x80006f20#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; decide
      have hpc2 : σ2.regs.get? Register.PC = some (0x80006f20#64 : BitVec 64) := by
        rw [obs_btaken_pc hobs2, hpceq]
      have ha2_2 := obs_btaken_other' hobs2 Register.x12 (by decide) ha2_1
      have ha3_2 := obs_btaken_other' hobs2 Register.x13 (by decide) ha3_1
      have hra_2 := obs_btaken_other' hobs2 Register.x1 (by decide) hra_1
      have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
        fun R hR => (sframe_btaken hobs2 R hR).trans (hframe_1 R hR)
      obtain ⟨vmi2, hmi2'⟩ := obs_btaken_minstret hobs2
      have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
      have hout2 : σ2.sailOutput = o :=
        (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
      refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), Or.inr (Or.inl ⟨24*j+8, ?_⟩)⟩
      exact ⟨hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hout2, hpc2, ha2_2, ha3_2,
        hra_2, ⟨vmi2, hmi2'⟩, hi2, hrega, hregb, hcstra, hcstrb, hpre, hnf, hwordeq, hframe_2⟩
  · have hguard : ((strlenWordVal (cwordAt m0 (pa.toNat + (24*j+8)))) != (BitVec.allOnes 64)) = true := by rw [bne_iff_ne]; exact hnul
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006ef0_taken c.σ c.tick c.steps (0x80006ef0#64) vmi
        (strlenWordVal (cwordAt m0 (pa.toNat + (24*j+8)))) (BitVec.allOnes 64)
        hgood hpc hmi ht0 ht2 hloaded rfl hguard htick
    have hpceq : (0x80006ef0#64 : BitVec 64) + sign_extend (m := 64) (0x00b4#13) = (0x80006fa4#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006fa4#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs1, hpceq]
    have hmem1eq : σ1.mem = c.σ.mem := hmem1
    have ha0_1 := obs_btaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_btaken_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_btaken_other' hobs1 Register.x12 (by decide) ha2
    have ha3_1 := obs_btaken_other' hobs1 Register.x13 (by decide) ha3
    have hra_1 := obs_btaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_btaken_minstret hobs1
    have hhasnul : csa.length < 24*j + 8 + 8 := by
      rcases Nat.lt_or_ge csa.length (24*j + 8 + 8) with hlt | hge
      · exact hlt
      · exact absurd (word_nul_free m0 pa csa hcstra (24*j+8) hge) hnul
    have hoff : nulOff (0x80006fa4#64 : BitVec 64) = 8 := by decide
    have hout1 : σ1.sailOutput = o :=
      (by chain_out [hobs1] : σ1.sailOutput = c.σ.sailOutput).trans hout
    refine ⟨⟨σ1, i1, c.steps + 1⟩, Steps.single hs1, Or.inr (Or.inr ⟨j, 0x80006fa4#64, ?_⟩)⟩
    exact ⟨Or.inr (Or.inl rfl), hG1, by rw [hmem1eq]; exact hloaded, by rw [hmem1eq]; exact hmem,
      hout1, hpc1, ha0_1, ha1_1, (by rw [hoff]; exact ha2_1), (by rw [hoff]; exact ha3_1), hra_1,
      ⟨vmi1, hmi1'⟩, hi1, hrega, hregb, hcstra, hcstrb, hmaskpin,
      (by rw [hoff]; exact hpre), (by rw [hoff]; omega), (by rw [hoff]; exact hjle), hframe_1⟩

/-- Group-2 straight-line `0xef8 → 0xf10`: `ld a2,16(a0)`; `ld a3,16(a1)`; four
magic-ALU ops. Produces `WGmid` at PC `0xf10`, offset `24j + 16`. -/
theorem wg2_straight (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WHead2 g pa pb r csa csb m0 o j)
      (WGmid g pa pb r csa csb m0 o j (24*j + 16) (0x80006f10#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, ha5, ht2, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, hpre, hjle, hframe⟩ := hSt
  have hjleb : 24*j + 16 ≤ csb.length := prefix_le_lenb hpre
  obtain ⟨htna, hloa, hhia, hhtifa, halgna⟩ := wcmp_load_bounds pa csa.length (24*j+16) hrega hjle (by omega)
  obtain ⟨htnb, hlob, hhib, hhtifb, halgnb⟩ := wcmp_load_bounds pb csb.length (24*j+16) hregb hjleb (by omega)
  rw [sext0_add] at hloa hhia hhtifa halgna hlob hhib hhtifb halgnb
  -- === ef8: ld a2,16(a0) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006ef8 c.σ c.tick c.steps (0x80006ef8#64) vmi (pa + BitVec.ofNat 64 (24*j))
      hgood hpc hmi ha0 hloaded rfl
      (by rw [word_off16]; exact hloa) (by rw [word_off16]; exact hhia)
      (by rw [word_off16]; exact hhtifa) (by rw [word_off16]; exact halgna) htick
  have hwordA : (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude c.σ) (0x80006ef8#64))
        (pa + BitVec.ofNat 64 (24*j) + sign_extend (m := 64) (0x010#12))))
      = cwordAt m0 (pa.toNat + (24*j + 16)) := by
    rw [word_off16, sext64_self, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem, htna]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006efc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006ef8#64) 4 = (0x80006efc#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha5_1 := obs_alu_other' hobs1 Register.x15 (by decide) ha5
  have ht2_1 := obs_alu_other' hobs1 Register.x7 (by decide) ht2
  have ha2_1 : σ1.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + (24*j+16))) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hwordA] at this
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === efc: ld a3,16(a1) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006efc σ1 i1 (c.steps + 1) (0x80006efc#64) vmi1 (pb + BitVec.ofNat 64 (24*j))
      hG1 hpc1 hmi1' ha1_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [word_off16]; exact hlob) (by rw [word_off16]; exact hhib)
      (by rw [word_off16]; exact hhtifb) (by rw [word_off16]; exact halgnb) hi1
  have hwordB : (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude σ1) (0x80006efc#64))
        (pb + BitVec.ofNat 64 (24*j) + sign_extend (m := 64) (0x010#12))))
      = cwordAt m0 (pb.toNat + (24*j + 16)) := by
    rw [word_off16, sext64_self, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem1, hmem, htnb]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006f00#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006efc#64) 4 = (0x80006f00#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have ha5_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha5_1
  have ht2_2 := obs_alu_other' hobs2 Register.x7 (by decide) ht2_1
  have ha3_2 : σ2.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + (24*j+16))) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hwordB] at this
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === f00: and t0,a2,a5 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006f00 σ2 i2 (c.steps + 1 + 1) (0x80006f00#64) vmi2 (cwordAt m0 (pa.toNat + (24*j+16))) magic7f
      hG2 hpc2 hmi2' ha2_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006f04#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006f00#64) 4 = (0x80006f04#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
  have ha3_3 := obs_alu_other' hobs3 Register.x13 (by decide) ha3_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have ht2_3 := obs_alu_other' hobs3 Register.x7 (by decide) ht2_2
  have ht0_3 : σ3.regs.get? Register.x5 = some (cwordAt m0 (pa.toNat + (24*j+16)) &&& magic7f) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.1 hR).trans (hframe_2 R hR)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === f04: or t1,a2,a5 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006f04 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006f04#64) vmi3 (cwordAt m0 (pa.toNat + (24*j+16))) magic7f
      hG3 hpc3 hmi3' ha2_3 ha5_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006f08#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006f04#64) 4 = (0x80006f08#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_alu_other' hobs4 Register.x11 (by decide) ha1_3
  have ha2_4 := obs_alu_other' hobs4 Register.x12 (by decide) ha2_3
  have ha3_4 := obs_alu_other' hobs4 Register.x13 (by decide) ha3_3
  have ha5_4 := obs_alu_other' hobs4 Register.x15 (by decide) ha5_3
  have ht2_4 := obs_alu_other' hobs4 Register.x7 (by decide) ht2_3
  have ht0_4 := obs_alu_other' hobs4 Register.x5 (by decide) ht0_3
  have ht1_4 : σ4.regs.get? Register.x6 = some (cwordAt m0 (pa.toNat + (24*j+16)) ||| magic7f) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs4 R hR.2.1 hR).trans (hframe_3 R hR)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === f08: add t0,t0,a5 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006f08 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006f08#64) vmi4
      (cwordAt m0 (pa.toNat + (24*j+16)) &&& magic7f) magic7f
      hG4 hpc4 hmi4' ht0_4 ha5_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006f0c#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006f08#64) 4 = (0x80006f0c#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ha2_5 := obs_alu_other' hobs5 Register.x12 (by decide) ha2_4
  have ha3_5 := obs_alu_other' hobs5 Register.x13 (by decide) ha3_4
  have ha5_5 := obs_alu_other' hobs5 Register.x15 (by decide) ha5_4
  have ht2_5 := obs_alu_other' hobs5 Register.x7 (by decide) ht2_4
  have ht1_5 := obs_alu_other' hobs5 Register.x6 (by decide) ht1_4
  have ht0_5 : σ5.regs.get? Register.x5 = some ((cwordAt m0 (pa.toNat + (24*j+16)) &&& magic7f) + magic7f) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs5 R hR.1 hR).trans (hframe_4 R hR)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === f0c: or t0,t0,t1 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006f0c σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006f0c#64) vmi5
      ((cwordAt m0 (pa.toNat + (24*j+16)) &&& magic7f) + magic7f) (cwordAt m0 (pa.toNat + (24*j+16)) ||| magic7f)
      hG5 hpc5 hmi5' ht0_5 ht1_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006f10#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006f0c#64) 4 = (0x80006f10#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_alu_other' hobs6 Register.x11 (by decide) ha1_5
  have ha2_6 := obs_alu_other' hobs6 Register.x12 (by decide) ha2_5
  have ha3_6 := obs_alu_other' hobs6 Register.x13 (by decide) ha3_5
  have ha5_6 := obs_alu_other' hobs6 Register.x15 (by decide) ha5_5
  have ht2_6 := obs_alu_other' hobs6 Register.x7 (by decide) ht2_5
  have ht0_6 : σ6.regs.get? Register.x5 = some (strlenWordVal (cwordAt m0 (pa.toNat + (24*j+16)))) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [strcmpWordVal_eq] at this
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have hframe_6 : ∀ R, NotWrittenStrcmp R → σ6.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs6 R hR.1 hR).trans (hframe_5 R hR)
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  have hmem6eq : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  have hout6 : σ6.sailOutput = o :=
    (by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5, hobs6] :
      σ6.sailOutput = c.σ.sailOutput).trans hout
  refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6), ?_⟩
  exact ⟨hG6, by rw [hmem6eq]; exact hloaded, by rw [hmem6eq]; exact hmem, hout6, hpc6, ha0_6, ha1_6,
    ha2_6, ha3_6, ha5_6, ht0_6, ht2_6, hra_6, ⟨vmi6, hmi6'⟩, hi6, hrega, hregb, hcstra, hcstrb,
    hmaskpin, hpre, hjle, hframe_6⟩

/-- Group-2 dispatch `0xf10 → {0xfb8, back-edge 0xeb8, 0xf20}`: `bne t0,t2 → fb8` (A-word
NUL); else `addi a0,24; addi a1,24; beq a2,a3 → eb8` (words equal → `WHead (j+1)`) |
fall-through to lane compare `0xf20` (words differ). -/
theorem wg2_dispatch (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WGmid g pa pb r csa csb m0 o j (24*j + 16) (0x80006f10#64))
      (fun c => WHead g pa pb r csa csb m0 o (j+1) c ∨ WordExit g pa pb r csa csb m0 o c) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, ha2, ha3, ha5, ht0, ht2, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, hpre, hjle, hframe⟩ := hSt
  by_cases hnul : strlenWordVal (cwordAt m0 (pa.toNat + (24*j+16))) = BitVec.allOnes 64
  · -- A NUL-free → f14/f18/f1c
    have hguard : ((strlenWordVal (cwordAt m0 (pa.toNat + (24*j+16)))) != (BitVec.allOnes 64)) = false := by rw [hnul]; simp
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006f10_nottaken c.σ c.tick c.steps (0x80006f10#64) vmi
        (strlenWordVal (cwordAt m0 (pa.toNat + (24*j+16)))) (BitVec.allOnes 64)
        hgood hpc hmi ht0 ht2 hloaded rfl hguard htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006f14#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006f10#64) 4 = (0x80006f14#64 : BitVec 64) from by decide] at this
    have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_bnottaken_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_bnottaken_other' hobs1 Register.x12 (by decide) ha2
    have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
    have ha5_1 := obs_bnottaken_other' hobs1 Register.x15 (by decide) ha5
    have ht2_1 := obs_bnottaken_other' hobs1 Register.x7 (by decide) ht2
    have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
    have hnf : 24*j + 16 + 8 ≤ csa.length := by
      rcases Nat.lt_or_ge csa.length (24*j + 16 + 8) with hlt | hge
      · exact absurd hnul (word_has_nul m0 pa csa hcstra (24*j+16) hjle hlt)
      · exact hge
    -- === f14: addi a0,a0,24 ===
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site_80006f14 σ1 i1 (c.steps + 1) (0x80006f14#64) vmi1 (pa + BitVec.ofNat 64 (24*j))
        hG1 hpc1 hmi1' ha0_1 (by rw [hmem1]; exact hloaded) rfl hi1
    have hpc2 : σ2.regs.get? Register.PC = some (0x80006f18#64 : BitVec 64) := by
      have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006f14#64) 4 = (0x80006f18#64 : BitVec 64) from by decide] at this
    have ha0_2 : σ2.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*(j+1))) := by
      have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [word_off24] at this
    have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
    have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
    have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
    have ha5_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha5_1
    have ht2_2 := obs_alu_other' hobs2 Register.x7 (by decide) ht2_1
    have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
    have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs2 R hR.2.2.2.1 hR).trans (hframe_1 R hR)
    obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
    -- === f18: addi a1,a1,24 ===
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_80006f18 σ2 i2 (c.steps + 1 + 1) (0x80006f18#64) vmi2 (pb + BitVec.ofNat 64 (24*j))
        hG2 hpc2 hmi2' ha1_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
    have hpc3 : σ3.regs.get? Register.PC = some (0x80006f1c#64 : BitVec 64) := by
      have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006f18#64) 4 = (0x80006f1c#64 : BitVec 64) from by decide] at this
    have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
    have ha1_3 : σ3.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*(j+1))) := by
      have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [word_off24] at this
    have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
    have ha3_3 := obs_alu_other' hobs3 Register.x13 (by decide) ha3_2
    have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
    have ht2_3 := obs_alu_other' hobs3 Register.x7 (by decide) ht2_2
    have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
    have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs3 R hR.2.2.2.2.1 hR).trans (hframe_2 R hR)
    obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
    by_cases hwordeq : cwordAt m0 (pa.toNat + (24*j+16)) = cwordAt m0 (pb.toNat + (24*j+16))
    · -- beq taken → eb8, WHead (j+1)
      have hguard2 : ((cwordAt m0 (pa.toNat + (24*j+16))) == (cwordAt m0 (pb.toNat + (24*j+16)))) = true := by rw [hwordeq]; simp
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site_80006f1c_taken σ3 i3 (c.steps + 1 + 1 + 1) (0x80006f1c#64) vmi3
          (cwordAt m0 (pa.toNat + (24*j+16))) (cwordAt m0 (pb.toNat + (24*j+16)))
          hG3 hpc3 hmi3' ha2_3 ha3_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hguard2 hi3
      have hpceq : (0x80006f1c#64 : BitVec 64) + sign_extend (m := 64) (0x1f9c#13) = (0x80006eb8#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; decide
      have hpc4 : σ4.regs.get? Register.PC = some (0x80006eb8#64 : BitVec 64) := by
        rw [obs_btaken_pc hobs4, hpceq]
      have ha0_4 := obs_btaken_other' hobs4 Register.x10 (by decide) ha0_3
      have ha1_4 := obs_btaken_other' hobs4 Register.x11 (by decide) ha1_3
      have ha5_4 := obs_btaken_other' hobs4 Register.x15 (by decide) ha5_3
      have ht2_4 := obs_btaken_other' hobs4 Register.x7 (by decide) ht2_3
      have hra_4 := obs_btaken_other' hobs4 Register.x1 (by decide) hra_3
      have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
        fun R hR => (sframe_btaken hobs4 R hR).trans (hframe_3 R hR)
      obtain ⟨vmi4, hmi4'⟩ := obs_btaken_minstret hobs4
      have hmem4eq : σ4.mem = c.σ.mem := by rw [hmem4, hmem3, hmem2, hmem1]
      have hpre1 : BytePrefix csa csb (24*j + 16 + 8) :=
        byte_prefix_extend m0 pa pb csa csb hcstra hcstrb (24*j+16) hpre (prefix_le_lenb hpre) hwordeq hnf
      have hout4 : σ4.sailOutput = o :=
        (by chain_out [hobs1, hobs2, hobs3, hobs4] : σ4.sailOutput = c.σ.sailOutput).trans hout
      refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩,
        (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4), Or.inl ?_⟩
      exact ⟨hG4, by rw [hmem4eq]; exact hloaded, by rw [hmem4eq]; exact hmem, hout4, hpc4, ha0_4, ha1_4,
        ha5_4, ht2_4, hra_4, ⟨vmi4, hmi4'⟩, hi4, hrega, hregb, hcstra, hcstrb, hmaskpin,
        (by rw [show 24*(j+1) = 24*j + 16 + 8 from by omega]; exact hpre1),
        (by rw [show 24*(j+1) = 24*j + 16 + 8 from by omega]; exact hnf), hframe_4⟩
    · -- beq not taken → f20, lane compare offset 24j+16
      have hguard2 : ((cwordAt m0 (pa.toNat + (24*j+16))) == (cwordAt m0 (pb.toNat + (24*j+16)))) = false := by
        rw [beq_eq_false_iff_ne]; exact hwordeq
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site_80006f1c_nottaken σ3 i3 (c.steps + 1 + 1 + 1) (0x80006f1c#64) vmi3
          (cwordAt m0 (pa.toNat + (24*j+16))) (cwordAt m0 (pb.toNat + (24*j+16)))
          hG3 hpc3 hmi3' ha2_3 ha3_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hguard2 hi3
      have hpc4 : σ4.regs.get? Register.PC = some (0x80006f20#64 : BitVec 64) := by
        have := obs_bnottaken_pc hobs4; rwa [show BitVec.addInt (0x80006f1c#64) 4 = (0x80006f20#64 : BitVec 64) from by decide] at this
      have ha2_4 := obs_bnottaken_other' hobs4 Register.x12 (by decide) ha2_3
      have ha3_4 := obs_bnottaken_other' hobs4 Register.x13 (by decide) ha3_3
      have hra_4 := obs_bnottaken_other' hobs4 Register.x1 (by decide) hra_3
      have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
        fun R hR => (sframe_bnottaken hobs4 R hR).trans (hframe_3 R hR)
      obtain ⟨vmi4, hmi4'⟩ := obs_bnottaken_minstret hobs4
      have hmem4eq : σ4.mem = c.σ.mem := by rw [hmem4, hmem3, hmem2, hmem1]
      have hout4 : σ4.sailOutput = o :=
        (by chain_out [hobs1, hobs2, hobs3, hobs4] : σ4.sailOutput = c.σ.sailOutput).trans hout
      refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩,
        (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4),
        Or.inr (Or.inl ⟨24*j+16, ?_⟩)⟩
      exact ⟨hG4, by rw [hmem4eq]; exact hloaded, by rw [hmem4eq]; exact hmem, hout4, hpc4, ha2_4, ha3_4,
        hra_4, ⟨vmi4, hmi4'⟩, hi4, hrega, hregb, hcstra, hcstrb, hpre, hnf, hwordeq, hframe_4⟩
  · -- A-word has NUL → fb8
    have hguard : ((strlenWordVal (cwordAt m0 (pa.toNat + (24*j+16)))) != (BitVec.allOnes 64)) = true := by rw [bne_iff_ne]; exact hnul
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006f10_taken c.σ c.tick c.steps (0x80006f10#64) vmi
        (strlenWordVal (cwordAt m0 (pa.toNat + (24*j+16)))) (BitVec.allOnes 64)
        hgood hpc hmi ht0 ht2 hloaded rfl hguard htick
    have hpceq : (0x80006f10#64 : BitVec 64) + sign_extend (m := 64) (0x00a8#13) = (0x80006fb8#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006fb8#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs1, hpceq]
    have hmem1eq : σ1.mem = c.σ.mem := hmem1
    have ha0_1 := obs_btaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_btaken_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_btaken_other' hobs1 Register.x12 (by decide) ha2
    have ha3_1 := obs_btaken_other' hobs1 Register.x13 (by decide) ha3
    have hra_1 := obs_btaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_btaken_minstret hobs1
    have hhasnul : csa.length < 24*j + 16 + 8 := by
      rcases Nat.lt_or_ge csa.length (24*j + 16 + 8) with hlt | hge
      · exact hlt
      · exact absurd (word_nul_free m0 pa csa hcstra (24*j+16) hge) hnul
    have hoff : nulOff (0x80006fb8#64 : BitVec 64) = 16 := by decide
    have hout1 : σ1.sailOutput = o :=
      (by chain_out [hobs1] : σ1.sailOutput = c.σ.sailOutput).trans hout
    refine ⟨⟨σ1, i1, c.steps + 1⟩, Steps.single hs1, Or.inr (Or.inr ⟨j, 0x80006fb8#64, ?_⟩)⟩
    exact ⟨Or.inr (Or.inr rfl), hG1, by rw [hmem1eq]; exact hloaded, by rw [hmem1eq]; exact hmem,
      hout1, hpc1, ha0_1, ha1_1, (by rw [hoff]; exact ha2_1), (by rw [hoff]; exact ha3_1), hra_1,
      ⟨vmi1, hmi1'⟩, hi1, hrega, hregb, hcstra, hcstrb, hmaskpin,
      (by rw [hoff]; exact hpre), (by rw [hoff]; omega), (by rw [hoff]; exact hjle), hframe_1⟩

/-- Group-0 dispatch emitting a STRUCTURED continue (`WHead1`) instead of the base's
thin PC/prefix fact, so the loop body can chain into group 1. Mirrors `wg0_dispatch`. -/
theorem wg0_dispatch2 (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WG0mid g pa pb r csa csb m0 o j)
      (fun c => WHead1 g pa pb r csa csb m0 o j c ∨ WordExit g pa pb r csa csb m0 o c) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, ha2, ha3, ha5, ht0, ht2, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, hpre, hjle, hframe⟩ := hSt
  by_cases hnul : strlenWordVal (cwordAt m0 (pa.toNat + 24*j)) = BitVec.allOnes 64
  · have hguard : ((strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) != (BitVec.allOnes 64)) = false := by rw [hnul]; simp
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006ed0_nottaken c.σ c.tick c.steps (0x80006ed0#64) vmi
        (strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) (BitVec.allOnes 64)
        hgood hpc hmi ht0 ht2 hloaded rfl hguard htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006ed4#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006ed0#64) 4 = (0x80006ed4#64 : BitVec 64) from by decide] at this
    have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_bnottaken_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_bnottaken_other' hobs1 Register.x12 (by decide) ha2
    have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
    have ha5_1 := obs_bnottaken_other' hobs1 Register.x15 (by decide) ha5
    have ht2_1 := obs_bnottaken_other' hobs1 Register.x7 (by decide) ht2
    have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
    have hnf : 24*j + 8 ≤ csa.length := by
      rcases Nat.lt_or_ge csa.length (24*j + 8) with hlt | hge
      · exact absurd hnul (word_has_nul m0 pa csa hcstra (24*j) hjle hlt)
      · exact hge
    by_cases hwordeq : cwordAt m0 (pa.toNat + 24*j) = cwordAt m0 (pb.toNat + 24*j)
    · have hguard2 : ((cwordAt m0 (pa.toNat + 24*j)) != (cwordAt m0 (pb.toNat + 24*j))) = false := by rw [hwordeq]; simp
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site_80006ed4_nottaken σ1 i1 (c.steps + 1) (0x80006ed4#64) vmi1
          (cwordAt m0 (pa.toNat + 24*j)) (cwordAt m0 (pb.toNat + 24*j))
          hG1 hpc1 hmi1' ha2_1 ha3_1 (by rw [hmem1]; exact hloaded) rfl hguard2 hi1
      have hpc2 : σ2.regs.get? Register.PC = some (0x80006ed8#64 : BitVec 64) := by
        have := obs_bnottaken_pc hobs2; rwa [show BitVec.addInt (0x80006ed4#64) 4 = (0x80006ed8#64 : BitVec 64) from by decide] at this
      have ha0_2 := obs_bnottaken_other' hobs2 Register.x10 (by decide) ha0_1
      have ha1_2 := obs_bnottaken_other' hobs2 Register.x11 (by decide) ha1_1
      have ha5_2 := obs_bnottaken_other' hobs2 Register.x15 (by decide) ha5_1
      have ht2_2 := obs_bnottaken_other' hobs2 Register.x7 (by decide) ht2_1
      have hra_2 := obs_bnottaken_other' hobs2 Register.x1 (by decide) hra_1
      have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
        fun R hR => (sframe_bnottaken hobs2 R hR).trans (hframe_1 R hR)
      obtain ⟨vmi2, hmi2'⟩ := obs_bnottaken_minstret hobs2
      have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
      have hpre1 : BytePrefix csa csb (24*j + 8) :=
        byte_prefix_extend m0 pa pb csa csb hcstra hcstrb (24*j) hpre (prefix_le_lenb hpre) hwordeq hnf
      have hout2 : σ2.sailOutput = o :=
        (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
      refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), Or.inl ?_⟩
      exact ⟨hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hout2, hpc2,
        ha0_2, ha1_2, ha5_2, ht2_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hrega, hregb, hcstra, hcstrb,
        hmaskpin, hpre1, hnf, hframe_2⟩
    · have hguard2 : ((cwordAt m0 (pa.toNat + 24*j)) != (cwordAt m0 (pb.toNat + 24*j))) = true := by rw [bne_iff_ne]; exact hwordeq
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site_80006ed4_taken σ1 i1 (c.steps + 1) (0x80006ed4#64) vmi1
          (cwordAt m0 (pa.toNat + 24*j)) (cwordAt m0 (pb.toNat + 24*j))
          hG1 hpc1 hmi1' ha2_1 ha3_1 (by rw [hmem1]; exact hloaded) rfl hguard2 hi1
      have hpceq : (0x80006ed4#64 : BitVec 64) + sign_extend (m := 64) (0x004c#13) = (0x80006f20#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; decide
      have hpc2 : σ2.regs.get? Register.PC = some (0x80006f20#64 : BitVec 64) := by
        rw [obs_btaken_pc hobs2, hpceq]
      have ha2_2 := obs_btaken_other' hobs2 Register.x12 (by decide) ha2_1
      have ha3_2 := obs_btaken_other' hobs2 Register.x13 (by decide) ha3_1
      have hra_2 := obs_btaken_other' hobs2 Register.x1 (by decide) hra_1
      have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
        fun R hR => (sframe_btaken hobs2 R hR).trans (hframe_1 R hR)
      obtain ⟨vmi2, hmi2'⟩ := obs_btaken_minstret hobs2
      have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
      have hout2 : σ2.sailOutput = o :=
        (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
      refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), Or.inr (Or.inl ⟨24*j, ?_⟩)⟩
      exact ⟨hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hout2, hpc2, ha2_2, ha3_2,
        hra_2, ⟨vmi2, hmi2'⟩, hi2, hrega, hregb, hcstra, hcstrb, hpre, hnf, hwordeq, hframe_2⟩
  · have hguard : ((strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) != (BitVec.allOnes 64)) = true := by rw [bne_iff_ne]; exact hnul
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006ed0_taken c.σ c.tick c.steps (0x80006ed0#64) vmi
        (strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) (BitVec.allOnes 64)
        hgood hpc hmi ht0 ht2 hloaded rfl hguard htick
    have hpceq : (0x80006ed0#64 : BitVec 64) + sign_extend (m := 64) (0x00dc#13) = (0x80006fac#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006fac#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs1, hpceq]
    have hmem1eq : σ1.mem = c.σ.mem := hmem1
    have ha0_1 := obs_btaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_btaken_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_btaken_other' hobs1 Register.x12 (by decide) ha2
    have ha3_1 := obs_btaken_other' hobs1 Register.x13 (by decide) ha3
    have hra_1 := obs_btaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_btaken_minstret hobs1
    have hhasnul : csa.length < 24*j + 8 := by
      rcases Nat.lt_or_ge csa.length (24*j + 8) with hlt | hge
      · exact hlt
      · exact absurd (word_nul_free m0 pa csa hcstra (24*j) hge) hnul
    have hoff : (24*j + nulOff (0x80006fac#64 : BitVec 64)) = 24*j := by
      rw [show nulOff (0x80006fac#64 : BitVec 64) = 0 from by decide, Nat.add_zero]
    have hout1 : σ1.sailOutput = o :=
      (by chain_out [hobs1] : σ1.sailOutput = c.σ.sailOutput).trans hout
    refine ⟨⟨σ1, i1, c.steps + 1⟩, Steps.single hs1, Or.inr (Or.inr ⟨j, 0x80006fac#64, ?_⟩)⟩
    exact ⟨Or.inl rfl, hG1, by rw [hmem1eq]; exact hloaded, by rw [hmem1eq]; exact hmem,
      hout1, hpc1, ha0_1, ha1_1, (by rw [hoff]; exact ha2_1), (by rw [hoff]; exact ha3_1), hra_1,
      ⟨vmi1, hmi1'⟩, hi1, hrega, hregb, hcstra, hcstrb, hmaskpin,
      (by rw [hoff]; exact hpre), (by rw [hoff]; omega), (by rw [hoff]; exact hjle), hframe_1⟩

/-! ## The full word-loop body and `Triple.loop` assembly

`wbody` composes the three groups: `WHead j → WG0mid → (WHead1 | exit) →
(WG1mid → (WHead2 | exit)) → (WG2mid → (WHead (j+1) | exit))`. The result is a
one-iteration step `Triple (WHead j) (WHead (j+1) ∨ WordExit)`. -/

/-- Group 0: `WHead j → WHead1 j ∨ WordExit`. -/
theorem wg0_body (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WHead g pa pb r csa csb m0 o j)
      (fun c => WHead1 g pa pb r csa csb m0 o j c ∨ WordExit g pa pb r csa csb m0 o c) :=
  (wg0_straight g pa pb r csa csb m0 o j).seq (wg0_dispatch2 g pa pb r csa csb m0 o j)

/-- Group 1: `WHead1 j → WHead2 j ∨ WordExit`. -/
theorem wg1_body (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WHead1 g pa pb r csa csb m0 o j)
      (fun c => WHead2 g pa pb r csa csb m0 o j c ∨ WordExit g pa pb r csa csb m0 o c) :=
  (wg1_straight g pa pb r csa csb m0 o j).seq (wg1_dispatch g pa pb r csa csb m0 o j)

/-- Group 2: `WHead2 j → WHead (j+1) ∨ WordExit`. -/
theorem wg2_body (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WHead2 g pa pb r csa csb m0 o j)
      (fun c => WHead g pa pb r csa csb m0 o (j+1) c ∨ WordExit g pa pb r csa csb m0 o c) :=
  (wg2_straight g pa pb r csa csb m0 o j).seq (wg2_dispatch g pa pb r csa csb m0 o j)

/-- **One loop iteration** `WHead j → WHead (j+1) ∨ WordExit`. Composes the three
groups; `WordExit` short-circuits to itself in each intermediate `cases`. -/
theorem wbody (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) :
    Triple (WHead g pa pb r csa csb m0 o j)
      (fun c => WHead g pa pb r csa csb m0 o (j+1) c ∨ WordExit g pa pb r csa csb m0 o c) := by
  -- WordExit → target (right injection)
  have hexit : Triple (WordExit g pa pb r csa csb m0 o)
      (fun c => WHead g pa pb r csa csb m0 o (j+1) c ∨ WordExit g pa pb r csa csb m0 o c) :=
    Triple.of_imp (fun _ h => Or.inr h)
  -- group 2: WHead2 ∨ WordExit → target
  have h2 : Triple (fun c => WHead2 g pa pb r csa csb m0 o j c ∨ WordExit g pa pb r csa csb m0 o c)
      (fun c => WHead g pa pb r csa csb m0 o (j+1) c ∨ WordExit g pa pb r csa csb m0 o c) :=
    Triple.cases (wg2_body g pa pb r csa csb m0 o j) hexit
  -- group 1: WHead1 ∨ WordExit → target (via group 2)
  have h1 : Triple (fun c => WHead1 g pa pb r csa csb m0 o j c ∨ WordExit g pa pb r csa csb m0 o c)
      (fun c => WHead g pa pb r csa csb m0 o (j+1) c ∨ WordExit g pa pb r csa csb m0 o c) :=
    Triple.cases ((wg1_body g pa pb r csa csb m0 o j).seq h2) hexit
  exact (wg0_body g pa pb r csa csb m0 o j).seq h1

/-! ### Loop invariant, guard, PC-guarded measure -/

/-- Loop invariant: at a head `WHead j` for some `j`, or at a word exit. -/
def SWLoopI (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  (∃ j, WHead g pa pb r csa csb m0 o j c) ∨ WordExit g pa pb r csa csb m0 o c

/-- Loop guard: at a head. -/
def SWLoopB (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ j, WHead g pa pb r csa csb m0 o j c

/-- PC-guarded measure: `la + 1 - 24j` at the head `0xeb8` (via `a0 = pa + 24j`),
else `0` (a `WordExit` PC drops the measure). -/
def SWLoopMu (pa : BitVec 64) (csa : List Char) (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x80006eb8#64)
  then csa.length + 1 - (((c.σ.regs.get? Register.x10).getD (0#64)).toNat - pa.toNat)
  else 0

/-- At a head, `SWLoopMu = la + 1 - 24j`. -/
theorem swloopmu_head (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) (c : Config)
    (hSt : WHead g pa pb r csa csb m0 o j c) :
    SWLoopMu pa csa c = csa.length + 1 - 24*j := by
  simp only [SWLoopMu, hSt.pc, hSt.a0, Option.getD_some, if_pos]
  have h : (pa + BitVec.ofNat 64 (24*j)).toNat = pa.toNat + 24*j :=
    ptrN pa (24*j) (by have := hSt.rega.nowrap; have := hSt.jle; omega)
  rw [h]; omega

/-- A `WordExit` config has PC ≠ `0xeb8`, so its measure is `0`. -/
theorem swloopmu_exit (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config)
    (hEx : WordExit g pa pb r csa csb m0 o c) :
    SWLoopMu pa csa c = 0 := by
  simp only [SWLoopMu]
  rcases hEx with ⟨n, hlane⟩ | ⟨j, pc, hnul⟩
  · rw [if_neg (by rw [hlane.pc]; intro h; injection h with h; exact absurd h (by decide))]
  · rw [if_neg (by rw [hnul.pcget]; intro h; injection h with h; rcases hnul.pcv with h1 | h1 | h1
                   <;> subst h1 <;> exact absurd h (by decide))]

/-- **Word-loop body** for `Triple.loop`: one iteration re-establishes `SWLoopI`
strictly decreasing `SWLoopMu`. Back-edge (`WHead (j+1)`): `24j ≤ la` and `24(j+1) ≤ la`
NOT required — the measure drops because `24j < 24(j+1)` and both are `≤ la+... `; we use
`24*j ≤ la` at the head (else no continue). Exit: measure `0`. -/
theorem swloop_body (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (nn : Nat) :
    Triple (fun c => SWLoopI g pa pb r csa csb m0 o c ∧ SWLoopB g pa pb r csa csb m0 o c
             ∧ SWLoopMu pa csa c = nn)
           (fun c => SWLoopI g pa pb r csa csb m0 o c ∧ SWLoopMu pa csa c < nn) := by
  intro c hc
  obtain ⟨_, ⟨j, hSt⟩, hmu⟩ := hc
  have hmu_eq : SWLoopMu pa csa c = csa.length + 1 - 24*j := swloopmu_head g pa pb r csa csb m0 o j c hSt
  rw [hmu_eq] at hmu
  have hjla : 24*j ≤ csa.length := hSt.jle
  obtain ⟨c1, hs1, hstep⟩ := wbody g pa pb r csa csb m0 o j c hSt
  rcases hstep with hHead | hExit
  · refine ⟨c1, hs1, Or.inl ⟨j+1, hHead⟩, ?_⟩
    have hmu1 : SWLoopMu pa csa c1 = csa.length + 1 - 24*(j+1) :=
      swloopmu_head g pa pb r csa csb m0 o (j+1) c1 hHead
    rw [hmu1, ← hmu]; omega
  · refine ⟨c1, hs1, Or.inr hExit, ?_⟩
    rw [swloopmu_exit g pa pb r csa csb m0 o c1 hExit]; omega

/-- The word loop runs from `SWLoopI` to `WordExit`. -/
theorem swloop_to_exit (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) :
    Triple (SWLoopI g pa pb r csa csb m0 o) (WordExit g pa pb r csa csb m0 o) := by
  have hloop := Triple.loop (I := SWLoopI g pa pb r csa csb m0 o)
    (B := SWLoopB g pa pb r csa csb m0 o) (SWLoopMu pa csa) (swloop_body g pa pb r csa csb m0 o)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hExit
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hExit⟩

/-! ## Lane-compare shift-equality bridges

The lane compare's `slli` probes test 2-byte blocks. `w <<< (8s) = w' <<< (8s)` iff the
low `64 - 8s` bits (bytes `[0, 8-s)`) agree — the shift discards the high bytes, keeping
the low bytes in the high lanes. These are pure `getLsbD` facts (no `bv_decide`),
the verified base for the (still-to-finish) lane first-difference arithmetic. -/

/-- `w <<< k = w' <<< k` (for `k ≤ 64`) iff the low `64 - k` bits agree. -/
theorem shiftLeft_eq_iff (w w' : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    (w <<< k = w' <<< k) ↔ (∀ i, i < 64 - k → w.getLsbD i = w'.getLsbD i) := by
  constructor
  · intro h i hi
    have := congrArg (fun x => x.getLsbD (i + k)) h
    simp only [BitVec.getLsbD_shiftLeft, show ¬ (i + k < k) from by omega,
      show i + k - k = i from by omega, decide_false, Bool.not_false, Bool.and_true] at this
    have hb : i + k < 64 := by omega
    simpa [hb] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_shiftLeft]
    by_cases hlt : i < k
    · simp [hlt]
    · have hik : i - k < 64 - k := by omega
      simp only [show (decide (i < k)) = false from by simp [hlt], Bool.not_false,
        Bool.and_true, h (i-k) hik]

/-- Byte `m` of `w`,`w'` agree, given the low `8*(8-s)` bits agree (`m < 8-s`). -/
theorem shiftLeft_bytes_agree (w w' : BitVec 64) (s : Nat)
    (h : ∀ i, i < 8*(8-s) → w.getLsbD i = w'.getLsbD i) (m : Nat) (hm : m < 8 - s) :
    w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i < 8 from hi), Bool.true_and]
  exact h (8*m + i) (by omega)

/-- **`slli` by `48` block-equality ⟺ bytes {0,1} agree.** (`slli_lane_eq` for s=6.) -/
theorem slli48_eq_iff (w w' : BitVec 64) :
    (w <<< (48:Nat) = w' <<< (48:Nat)) ↔
      (∀ m, m < 2 → w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8) := by
  rw [shiftLeft_eq_iff w w' 48 (by omega)]
  constructor
  · intro h m hm; exact shiftLeft_bytes_agree w w' 6 (by simpa using h) m (by omega)
  · intro h i hi
    have hm : i / 8 < 2 := by omega
    have := congrArg (fun x => x.getLsbD (i % 8)) (h (i/8) hm)
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i % 8 < 8 from Nat.mod_lt _ (by decide)),
      Bool.true_and, show 8*(i/8) + i%8 = i from by omega] at this
    exact this

/-! ## Closing note — what lands (part 2), and the remaining lane/NUL/entry plan

**Complete & fully proved in this file (`StrcmpSpecW2`):**

* **Shift/pointer arithmetic.** `shl_48/32/16`, `shr_48` (`slli/srli` shamt reductions
  to `<<< N`/`>>> N`); `word_off8/16/24` (group-`g` load-pointer identities).
* **Groups 1 and 2, end-to-end.** `wg1_straight`+`wg1_dispatch` (offset `24j+8`,
  `0xed8…0xef4`, three-way exit to `WHead2`/lane/NUL@`0xfa4`) and `wg2_straight`+
  `wg2_dispatch` (offset `24j+16`, `0xef8…0xf1c`, with the **back-edge** `addi a0,24;
  addi a1,24; beq a2,a3 → 0xeb8` re-establishing `WHead (j+1)` and `BytePrefix (24j+24)`
  via `byte_prefix_extend`, else fall to lane compare | NUL@`0xfb8`).
* **A structured group-0 dispatch** `wg0_dispatch2` (emits `WHead1` on continue,
  unlike the base's thin fact), so the three groups compose.
* **The full word-loop assembly.** `wbody : Triple (WHead j) (WHead (j+1) ∨ WordExit)`
  (composes the three groups; `WordExit` short-circuits in each `Triple.cases`), and
  `swloop_to_exit : Triple SWLoopI (WordExit)` via `Triple.loop` with the PC-guarded
  measure `SWLoopMu = if PC = 0xeb8 then la+1−24j else 0` (`swloopmu_head`/`swloopmu_exit`,
  `swloop_body`). `WordExit` bundles the lane-compare state `WLaneCmp n` and the three
  NUL-block PC-tagged terminals with their `n ≤ la < n+8` / `BytePrefix n` byte facts.
* **The lane shift-equality bridges.** `shiftLeft_eq_iff`, `shiftLeft_bytes_agree`,
  `slli48_eq_iff` (`slli`-block equality ⟺ per-byte agreement) — the verified base for
  the first-difference-byte lane arithmetic.

**What remains (unchanged plan, priorities 3–5):**

3. **Lane compare** `WLaneCmp n → BF9c` (`0xf20 … 0xf80`). The `slli48_eq_iff` family
   (extend to `slli32`/`slli16` by the same `shiftLeft_eq_iff` route) locates the
   2-byte block holding the first difference; `srli 0x30` + `zext.b` (`srli_byte`)
   extracts the differing byte; `sub`/`zext_toNat`/`strcmpSign_sub` give the sign. The
   genuinely new content is the **16-bit-block subtraction borrow analysis**: the `f58`/
   `f70` early-`ret` returns the block difference `(w>>>48) − (w'>>>48)` directly, whose
   SIGN must be shown equal to `isign (byteVal csa d) (byteVal csb d)` for the first
   differing byte `d` in the block, and the `bnez a1 → f74` re-extract handles the case
   where the low byte of the block agrees but the high byte differs. Both paths must
   land the SAME `hsign : isign (byteVal csa d) (byteVal csb d) = strcmpSpecSign csa csb`
   (via `strcmpSpecSign_at` with `BytePrefix csa csb d` from the located `d`), plugging
   into the base's `byte_f9c_ret`.
4. **NUL-word exit blocks** `0xfac/0xfa4/0xfb8` (+ shared `0xfb0` `li a0,0; ret` and the
   group-2 `0xfc0/0xfc4/0xfc8`). Structure now fully mapped: group-0 jumps to `0xfac`
   directly; group-1 advances `a0/a1` by 8 (`0xfa4/0xfa8`) then `0xfac`; group-2 by 16
   (`0xfb8/0xfbc`) then `0xfc0`. At the `bne a2,a3` test: if words EQUAL (A's word has the
   NUL, so both strings terminate at `la = lb`) → `li a0,0; ret` = result `0`
   (`strcmpSpecSign = 0` via `strcmpSpecSign_eq`); if words DIFFER → jump to byte loop
   `0xf84` at the ADVANCED pointer `pa+n`. The byte-loop entry needs a **suffix bridge**:
   `BSt` at base `pa+n` with `csa' = csa.drop n`, plus
   `strcmpSpecSign (drop n csa) (drop n csb) = strcmpSpecSign csa csb` under
   `BytePrefix csa csb n` (agree+nonzero on `[0,n)`).
5. **Aligned entry** `strcmp_word_spec` (`0xea0 … 0xeb4`: `or a4; li t2,-1; andi a4,7;
   bnez a4` NOT taken → `auipc a5; ld a5,mask`) establishing `WHead 0` (`t2 = allOnes`
   via `neg_one_allOnes`, `a5 = magic7f` via `ldBytesT_mask`, `BytePrefix … 0` trivial),
   then `swloop_to_exit` → lane/NUL → `BDone`; and `strcmp_full_spec` = `Triple.cases`
   over the entry alignment test unifying with `StrcmpSpec.strcmp_byte_path` (both
   `BDone`, same `Q`).

**New gotchas (this file).**
1. `WLoopI/WLoopB/WLoopMu/wloopmu_head/wloop_body` COLLIDE with `StrlenSpec`'s (same
   `Vsa.Sim` namespace, transitively imported) — renamed to `SWLoop*`/`swloop*`.
2. Group-`g` load bounds: `wcmp_load_bounds` states them on `((p+ofNat n)+sext 0)`, but
   the offset-8/16 `ld` sites want them on `(p+ofNat 24j)+sext(8/16)`. Bridge with
   `rw [sext0_add] at …` (strip the `+ sext 0`) then `rw [word_off8/16]` per hypothesis.
3. `beq` guard false-case: `rw [beq_eq_false_iff_ne]; exact hne` (the group-2 back-edge
   `beq a2,a3` fall-through). `bne` true-case stays `rw [bne_iff_ne]`.
4. `BitVec.getLsbD_shiftLeft` emits `decide (i<64) && …` and `!decide (i<k)` guards, not
   clean `if`s — discharge with `simp only [show decide (i<k) = false from …, …]`, not
   `rw [if_neg]`.
-/

end Vsa.Sim

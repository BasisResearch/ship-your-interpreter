import Vsa.Sim.ValueEqualSites
import Vsa.Sim.ValueTruthySpec

/-!
# Layer 3 — total-correctness spec for `value_equal` (@0x8000285c)

`value_equal(Value a, Value b)` (both by-reference in `a0`/`a1`) returns
`cond (Value.equal va vb) 1 0` in `a0`. It:

1. loads both kind tags, `bne` to the `return 0` tail if they differ;
2. an out-of-range guard (`li a4,5; bltu a4,a5 → return 0`);
3. dispatches through a `.rodata` jump table to a per-kind handler.

Handlers (all read-only): null → `1`; bool/int/closure/native → payload `sub`
then `seqz` (0 iff equal); str → `strcmp(...) == 0`.

This file proves the **five non-`str` variants** end-to-end. The jump-table entries
are provided as a `JumpTable` region hypothesis; `φc`/`N.addr` injectivity bridge the
closure/native cases (the C compares pointers, the spec compares addresses/`NativeFn`).

## C ↔ spec correspondence (checked against `c/src/value.c` + `Value.equal`)

| kind    | C                          | spec `Value.equal`        | bridge                    |
|---------|----------------------------|---------------------------|---------------------------|
| null    | `return 1`                 | `true`                    | `cond … 1 0 = 1`          |
| bool    | `a.as.b == b.as.b`         | `a == b`                  | 4-byte payloads {0,1}     |
| int     | `a.as.i == b.as.i`         | `a == b` (Int)            | two's-complement 8-byte   |
| str     | `strcmp(...) == 0`         | `a == b` (String)         | `strcmp_full_spec`        |
| closure | `a.as.fn == b.as.fn`       | `a == b` (Addr)           | **`φc` injectivity**      |
| native  | `a.as.native.fn == …`      | `a == b` (NativeFn)       | **`N.addr` injectivity**  |

The closure case compares `Closure*` pointers (`φc ca` vs `φc cb`); with `φc`
injective on the relevant addresses these agree with the spec's address equality.
The native case compares the three fn pointers `N.addr f`; with those three distinct,
pointer equality agrees with `NativeFn` equality.
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

/-! ## Ghost frame for `value_equal` (non-str path)

The non-str paths write scratch GPRs `x10` (a0 result / payload), `x14` (a4),
`x15` (a5), plus control/noise registers. `NotWrittenVE` is the disequality set for
a ghost register untouched by these paths. -/
abbrev NotWrittenVE (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-! ## Region facts for the two argument buffers

Each 24-byte `Value` lives in RAM, 8-aligned, above the HTIF window, disjoint from
the `value_equal` code `[0x8000285c, 0x800028fc)`. -/
structure VERegion (buf : BitVec 64) : Prop where
  align : buf.toNat % 8 = 0
  lo : 0x80000000 ≤ buf.toNat
  hi : buf.toNat + 24 ≤ 0x100000000
  win : tohostAddr + 16 ≤ buf.toNat

theorem ve_kind_addr (buf : BitVec 64) :
    (buf + sign_extend (m := 64) (0x000#12)).toNat = buf.toNat := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide]
  rw [BitVec.add_zero]

theorem ve_pay8_addr (buf : BitVec 64) (hr : VERegion buf) :
    (buf + sign_extend (m := 64) (0x008#12)).toNat = buf.toNat + 8 := by
  have hsext : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := hr.hi
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ve_pay16_addr (buf : BitVec 64) (hr : VERegion buf) :
    (buf + sign_extend (m := 64) (0x010#12)).toNat = buf.toNat + 16 := by
  have hsext : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := hr.hi
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## The `.rodata` jump table at `0x80019ef8`

Six signed 32-bit offsets (kind 0..5), each `entry_k` such that
`entry_k + 0x80019ef8` is the kind-`k` handler address. Read off the linked image
(`objdump -s -j .rodata`). Provided as a hypothesis (like `*Loaded` for code). -/
def JumpTable (m : Mem) : Prop :=
  -- kind 0 → 0x800028a8 : bytes b0 89 fe ff
  m[(0x80019ef8 : Nat)]? = some (0xb0#8) ∧ m[(0x80019ef9 : Nat)]? = some (0x89#8) ∧
  m[(0x80019efa : Nat)]? = some (0xfe#8) ∧ m[(0x80019efb : Nat)]? = some (0xff#8) ∧
  -- kind 1 → 0x800028b0 : bytes b8 89 fe ff
  m[(0x80019efc : Nat)]? = some (0xb8#8) ∧ m[(0x80019efd : Nat)]? = some (0x89#8) ∧
  m[(0x80019efe : Nat)]? = some (0xfe#8) ∧ m[(0x80019eff : Nat)]? = some (0xff#8) ∧
  -- kind 2 → 0x80002894 : bytes 9c 89 fe ff
  m[(0x80019f00 : Nat)]? = some (0x9c#8) ∧ m[(0x80019f01 : Nat)]? = some (0x89#8) ∧
  m[(0x80019f02 : Nat)]? = some (0xfe#8) ∧ m[(0x80019f03 : Nat)]? = some (0xff#8) ∧
  -- kind 3 → 0x800028c4 : bytes cc 89 fe ff
  m[(0x80019f04 : Nat)]? = some (0xcc#8) ∧ m[(0x80019f05 : Nat)]? = some (0x89#8) ∧
  m[(0x80019f06 : Nat)]? = some (0xfe#8) ∧ m[(0x80019f07 : Nat)]? = some (0xff#8) ∧
  -- kind 4 → 0x80002894 : bytes 9c 89 fe ff
  m[(0x80019f08 : Nat)]? = some (0x9c#8) ∧ m[(0x80019f09 : Nat)]? = some (0x89#8) ∧
  m[(0x80019f0a : Nat)]? = some (0xfe#8) ∧ m[(0x80019f0b : Nat)]? = some (0xff#8) ∧
  -- kind 5 → 0x800028e8 : bytes f0 89 fe ff
  m[(0x80019f0c : Nat)]? = some (0xf0#8) ∧ m[(0x80019f0d : Nat)]? = some (0x89#8) ∧
  m[(0x80019f0e : Nat)]? = some (0xfe#8) ∧ m[(0x80019f0f : Nat)]? = some (0xff#8)

/-- The handler address for a spec value's kind (target of the computed jump). -/
def handlerAddr : Value → BitVec 64
  | .null => 0x800028a8#64
  | .bool _ => 0x800028b0#64
  | .int _ => 0x80002894#64
  | .str _ => 0x800028c4#64
  | .closure _ => 0x80002894#64
  | .native _ => 0x800028e8#64

/-- The four little-endian jump-table bytes for a kind (as a tuple). -/
def jtBytes : Value → (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)
  | .null => (0xb0#8, 0x89#8, 0xfe#8, 0xff#8)
  | .bool _ => (0xb8#8, 0x89#8, 0xfe#8, 0xff#8)
  | .int _ => (0x9c#8, 0x89#8, 0xfe#8, 0xff#8)
  | .str _ => (0xcc#8, 0x89#8, 0xfe#8, 0xff#8)
  | .closure _ => (0x9c#8, 0x89#8, 0xfe#8, 0xff#8)
  | .native _ => (0xf0#8, 0x89#8, 0xfe#8, 0xff#8)

/-- The computed jump target from the table bytes lands on `handlerAddr v`.
`(sext(t3++t2++t1++t0) + 0x80019ef8) + sext 0`, bit-0 cleared. -/
theorem jt_target (v : Value) :
    let (t0, t1, t2, t3) := jtBytes v
    (BitVec.update
      ((sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4)))
        + (0x80019ef8#64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = handlerAddr v := by
  cases v <;> (simp only [jtBytes, handlerAddr]; apply BitVec.eq_of_toNat_eq; decide)

/-- The base register `a4 = 0x80019870 + sext 0x688 = 0x80019ef8` (the table base). -/
theorem jt_base :
    (0x80002870#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)
      + sign_extend (m := 64) (0x688#12) = 0x80019ef8#64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The table-index address `a5 = (kind <<< 2) + 0x80019ef8 = 0x80019ef8 + 4*kind`.
Uses `shift_bits_left (ofNat kind) 2` with `kind < 6`. -/
theorem jt_index_addr (kind : Nat) (hk : kind < 6) :
    (shift_bits_left (BitVec.ofNat 64 kind) (Sail.BitVec.extractLsb (0x02#6) 5 0)
        + (0x80019ef8#64) + sign_extend (m := 64) (0x000#12)).toNat
      = 0x80019ef8 + 4 * kind := by
  match kind, hk with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide

/-- From `JumpTable m`, the four table bytes at index `4 * kindTag v` are `jtBytes v`. -/
theorem jt_read (m : Mem) (v : Value) (h : JumpTable m) :
    let (t0, t1, t2, t3) := jtBytes v
    m[(0x80019ef8 + 4 * kindTag v)]? = some t0 ∧ m[(0x80019ef8 + 4 * kindTag v) + 1]? = some t1 ∧
    m[(0x80019ef8 + 4 * kindTag v) + 2]? = some t2 ∧ m[(0x80019ef8 + 4 * kindTag v) + 3]? = some t3 := by
  obtain ⟨a0,a1,a2,a3, b0,b1,b2,b3, c0,c1,c2,c3, d0,d1,d2,d3, e0,e1,e2,e3, f0,f1,f2,f3⟩ := h
  cases v <;>
    simp only [jtBytes, kindTag] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | exact a0 | exact a1 | exact a2 | exact a3
      | exact b0 | exact b1 | exact b2 | exact b3
      | exact c0 | exact c1 | exact c2 | exact c3
      | exact d0 | exact d1 | exact d2 | exact d3
      | exact e0 | exact e1 | exact e2 | exact e3
      | exact f0 | exact f1 | exact f2 | exact f3

/-! ## Pre / post -/

def ve_pre (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Value_equalLoaded c.σ.mem ∧ JumpTable c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x8000285c#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some bufa ∧ c.σ.regs.get? Register.x11 = some bufb ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
  ValueRepr m0 N φc bufa.toNat va ∧ ValueRepr m0 N φc bufb.toNat vb ∧
  VERegion bufa ∧ VERegion bufb ∧
  (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenVE R → c.σ.regs.get? R = g R)

def ve_post (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64) (va vb : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  c.σ.regs.get? Register.x10 = some (cond (Value.equal va vb) (1#64) (0#64)) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
  c.σ.mem = m0 ∧
  (∀ R : Register, NotWrittenVE R → c.σ.regs.get? R = g R)

/-! ## Ghost-frame passthrough per step-shape (mirror `ValueTruthySpec.frame_*_t`) -/

theorem frame_alu_ve {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hR : NotWrittenVE R) (hrd : (rd == R) = false) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

theorem frame_branch_taken_ve {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenVE R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

theorem frame_branch_nottaken_ve {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenVE R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

theorem frame_jr_ve {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenVE R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## The dispatch spine (0x80002870 → handler)

From a state at `0x80002870` with `x15 = ofNat (kindTag v)` (kind already known
equal + in range) and the jump table loaded, run the 7 dispatch instructions
(`auipc/addi/slli/add/lw/add/jr`) to land at `handlerAddr v`, preserving the two
buffer pointers, `x1`, memory, and the ghost frame. -/
theorem ve_dispatch (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (v : Value) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0)
    (hloaded : Value_equalLoaded m0) (hjt : JumpTable m0)
    (hpc : σ.regs.get? Register.PC = some (0x80002870#64 : BitVec 64))
    (hx15 : σ.regs.get? Register.x15 = some (BitVec.ofNat 64 (kindTag v)))
    (ha0 : σ.regs.get? Register.x10 = some bufa) (ha1 : σ.regs.get? Register.x11 = some bufb)
    (hra : σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps c ⟨σ2, i2, steps0 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧ σ2.mem = m0 ∧
      σ2.regs.get? Register.PC = some (handlerAddr v) ∧
      σ2.regs.get? Register.x10 = some bufa ∧ σ2.regs.get? Register.x11 = some bufb ∧
      σ2.regs.get? Register.x1 = some r ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R) := by
  have hktlt : kindTag v < 6 := by cases v <;> simp [kindTag]
  have hkt6 : (kindTag v) < 128 := by omega
  -- === 0x80002870: auipc a4 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002870 σ i steps0 (0x80002870#64) vmi hG hpc hmi (hmem ▸ hloaded) rfl hi
  have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002874#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002870#64) 4 = (0x80002874#64 : BitVec 64) from by decide] at this
  have ha4_1 : σ1.regs.get? Register.x14
      = some ((0x80002870#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx15_1 := obs_alu_other hobs1 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenVE R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs1 R hR hR.2.1).trans (hframe R hR)
  -- === 0x80002874: addi a4,a4,0x688 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002874 σ1 i1 (steps0 + 1) (0x80002874#64) vmi1 _ hG1 hpc1 hmi1 ha4_1 (hmem1eq.symm ▸ hloaded) rfl hi1
  have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002878#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80002874#64) 4 = (0x80002878#64 : BitVec 64) from by decide] at this
  have ha4_2 : σ2.regs.get? Register.x14 = some (0x80019ef8#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [jt_base] at this
  have hx15_2 := obs_alu_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_1
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs2 R hR hR.2.1).trans (hframe1 R hR)
  -- === 0x80002878: slli a5,a5,2 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002878 σ2 i2 (steps0 + 1 + 1) (0x80002878#64) vmi2 _ hG2 hpc2 hmi2 hx15_2 (hmem2eq.symm ▸ hloaded) rfl hi2
  have hmem3eq : σ3.mem = m0 := by rw [hmem3, hmem2eq]
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000287c#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80002878#64) 4 = (0x8000287c#64 : BitVec 64) from by decide] at this
  have hx15_3 : σ3.regs.get? Register.x15
      = some (shift_bits_left (BitVec.ofNat 64 (kindTag v)) (Sail.BitVec.extractLsb (0x02#6) 5 0)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha4_3 := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_2
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hframe3 : ∀ R : Register, NotWrittenVE R → σ3.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs3 R hR hR.2.2.1).trans (hframe2 R hR)
  -- === 0x8000287c: add a5,a5,a4 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_8000287c σ3 i3 (steps0 + 1 + 1 + 1) (0x8000287c#64) vmi3 _ _ hG3 hpc3 hmi3 hx15_3 ha4_3 (hmem3eq.symm ▸ hloaded) rfl hi3
  have hmem4eq : σ4.mem = m0 := by rw [hmem4, hmem3eq]
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002880#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x8000287c#64) 4 = (0x80002880#64 : BitVec 64) from by decide] at this
  have hx15_4 : σ4.regs.get? Register.x15
      = some (shift_bits_left (BitVec.ofNat 64 (kindTag v)) (Sail.BitVec.extractLsb (0x02#6) 5 0)
              + (0x80019ef8#64)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha4_4 := obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_3
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 := obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hframe4 : ∀ R : Register, NotWrittenVE R → σ4.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs4 R hR hR.2.2.1).trans (hframe3 R hR)
  -- === 0x80002880: lw a5,0(a5) (JUMP-TABLE READ) ===
  -- name the four table bytes via the projections of `jtBytes v`
  let t0 := (jtBytes v).1
  let t1 := (jtBytes v).2.1
  let t2 := (jtBytes v).2.2.1
  let t3 := (jtBytes v).2.2.2
  have ht0def : t0 = (jtBytes v).1 := rfl
  have ht1def : t1 = (jtBytes v).2.1 := rfl
  have ht2def : t2 = (jtBytes v).2.2.1 := rfl
  have ht3def : t3 = (jtBytes v).2.2.2 := rfl
  have hjtr : m0[(0x80019ef8 + 4 * kindTag v)]? = some t0 ∧
      m0[(0x80019ef8 + 4 * kindTag v) + 1]? = some t1 ∧
      m0[(0x80019ef8 + 4 * kindTag v) + 2]? = some t2 ∧
      m0[(0x80019ef8 + 4 * kindTag v) + 3]? = some t3 := jt_read m0 v hjt
  obtain ⟨ht0, ht1, ht2, ht3⟩ := hjtr
  have hidx : (shift_bits_left (BitVec.ofNat 64 (kindTag v)) (Sail.BitVec.extractLsb (0x02#6) 5 0)
      + (0x80019ef8#64) + sign_extend (m := 64) (0x000#12)).toNat = 0x80019ef8 + 4 * kindTag v :=
    jt_index_addr (kindTag v) hktlt
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002880 σ4 i4 (steps0 + 1 + 1 + 1 + 1) (0x80002880#64) vmi4 _ t0 t1 t2 t3
      hG4 hpc4 hmi4 hx15_4 (hmem4eq.symm ▸ hloaded) rfl
      (by rw [hidx]; omega)
      (by rw [hidx]; omega)
      (by rw [hidx]; exact Or.inl (by show _ + _ + 4 ≤ tohostAddr; rw [show tohostAddr = 0x8001ad00 from rfl]; omega))
      (by rw [hidx]; omega)
      (by rw [hidx, hmem4eq]; exact ht0) (by rw [hidx, hmem4eq]; exact ht1)
      (by rw [hidx, hmem4eq]; exact ht2) (by rw [hidx, hmem4eq]; exact ht3) hi4
  have hmem5eq : σ5.mem = m0 := by rw [hmem5, hmem4eq]
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002884#64 : BitVec 64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80002880#64) 4 = (0x80002884#64 : BitVec 64) from by decide] at this
  have hx15_5 : σ5.regs.get? Register.x15
      = some (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha4_5 := obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_4
  have ha0_5 := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have ha1_5 := obs_alu_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_4
  have hra_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hframe5 : ∀ R : Register, NotWrittenVE R → σ5.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs5 R hR hR.2.2.1).trans (hframe4 R hR)
  -- === 0x80002884: add a5,a5,a4 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80002884 σ5 i5 (steps0 + 1 + 1 + 1 + 1 + 1) (0x80002884#64) vmi5 _ _ hG5 hpc5 hmi5 hx15_5 ha4_5 (hmem5eq ▸ hloaded) rfl hi5
  have hmem6eq : σ6.mem = m0 := by rw [hmem6, hmem5eq]
  have hpc6 : σ6.regs.get? Register.PC = some (0x80002888#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80002884#64) 4 = (0x80002888#64 : BitVec 64) from by decide] at this
  have hx15_6 : σ6.regs.get? Register.x15
      = some (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
              + (0x80019ef8#64)) :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha0_6 := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
  have ha1_6 := obs_alu_other hobs6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_5
  have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hframe6 : ∀ R : Register, NotWrittenVE R → σ6.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs6 R hR hR.2.2.1).trans (hframe5 R hR)
  -- === 0x80002888: jr a5 (computed jump to handler) ===
  have htgteq : (BitVec.update (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
              + (0x80019ef8#64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = handlerAddr v :=
    jt_target v
  have htgt : (BitVec.update (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
              + (0x80019ef8#64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [htgteq]; cases v <;> (simp only [handlerAddr]; decide)
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80002888 σ6 i6 (steps0 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002888#64) vmi6
      (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4)) + (0x80019ef8#64))
      hG6 hpc6 hmi6 hx15_6 (hmem6eq ▸ hloaded) rfl htgt hi6
  have hmem7eq : σ7.mem = m0 := by rw [hmem7, hmem6eq]
  have hpc7 : σ7.regs.get? Register.PC = some (handlerAddr v) := by
    have := obs_jr_pc hobs7; rw [htgteq] at this; exact this
  have ha0_7 := obs_jr_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_6
  have ha1_7 := obs_jr_other hobs7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_6
  have hra_7 := obs_jr_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6
  have hframe7 : ∀ R : Register, NotWrittenVE R → σ7.regs.get? R = g R := fun R hR =>
    (frame_jr_ve hobs7 R hR).trans (hframe6 R hR)
  refine ⟨σ7, i7,
    (((((((hsteps0.trans (Steps.single hs1)).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans (Steps.single hs7)),
    hi7, hG7, hmem7eq, hpc7, ha0_7, ha1_7, hra_7, obs_jr_minstret hobs7, hframe7⟩

/-! ## The prefix (entry → dispatch, equal-kind case)

Runs 0x8000285c..0x8000286c (both kind loads, the `bne` (not taken because kinds
equal), `li a4,5`, `bltu` (not taken because kind ≤ 5)) landing at 0x80002870 with
`x15 = ofNat (kindTag vb)`, ready for `ve_dispatch`. Requires `kindTag va = kindTag vb`. -/
theorem ve_prefix (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config)
    (hG : GoodState c.σ) (hloaded : Value_equalLoaded c.σ.mem) (hmem : c.σ.mem = m0)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000285c#64 : BitVec 64))
    (ha0 : c.σ.regs.get? Register.x10 = some bufa) (ha1 : c.σ.regs.get? Register.x11 = some bufb)
    (hra : c.σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (htick : c.tick < 2)
    (hra' : ValueRepr m0 N φc bufa.toNat va) (hrb' : ValueRepr m0 N φc bufb.toNat vb)
    (hrega : VERegion bufa) (hregb : VERegion bufb)
    (hkeq : kindTag va = kindTag vb)
    (hframe : ∀ R : Register, NotWrittenVE R → c.σ.regs.get? R = g R) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps c ⟨σ2, i2, c.steps + 1 + 1 + 1 + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧ σ2.mem = m0 ∧
      σ2.regs.get? Register.PC = some (0x80002870#64 : BitVec 64) ∧
      σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 (kindTag vb)) ∧
      σ2.regs.get? Register.x10 = some bufa ∧ σ2.regs.get? Register.x11 = some bufb ∧
      σ2.regs.get? Register.x1 = some r ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hloaded0 : Value_equalLoaded m0 := hmem ▸ hloaded
  have hka : read32 m0 bufa.toNat = some (kindTag va) := kind_read32 m0 N φc bufa.toNat va hra'
  have hkb : read32 m0 bufb.toNat = some (kindTag vb) := kind_read32 m0 N φc bufb.toNat vb hrb'
  obtain ⟨a0, a1, a2, a3, ha0b, ha1b, ha2b, ha3b, hareca⟩ := read32_bytes m0 bufa.toNat _ hka
  obtain ⟨c0, c1, c2, c3, hc0b, hc1b, hc2b, hc3b, hrecb⟩ := read32_bytes m0 bufb.toNat _ hkb
  have hkalt : kindTag va < 128 := by cases va <;> simp [kindTag]
  have hkblt : kindTag vb < 128 := by cases vb <;> simp [kindTag]
  have hkalign_a : bufa.toNat % 4 = 0 := by have := hrega.align; omega
  have hkalign_b : bufb.toNat % 4 = 0 := by have := hregb.align; omega
  -- === 0x8000285c: lw a4,0(a0) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000285c c.σ c.tick c.steps (0x8000285c#64) vmi bufa a0 a1 a2 a3 hG hpc hmi ha0 hloaded rfl
      (by rw [ve_kind_addr]; exact hrega.lo) (by rw [ve_kind_addr]; have := hrega.hi; omega)
      (by rw [ve_kind_addr]; right; rw [htoh]; have := hrega.win; rw [htoh] at this; omega)
      (by rw [ve_kind_addr]; exact hkalign_a)
      (by rw [ve_kind_addr, hmem]; exact ha0b) (by rw [ve_kind_addr, hmem]; exact ha1b)
      (by rw [ve_kind_addr, hmem]; exact ha2b) (by rw [ve_kind_addr, hmem]; exact ha3b) htick
  have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002860#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000285c#64) 4 = (0x80002860#64 : BitVec 64) from by decide] at this
  have ha14_1 : σ1.regs.get? Register.x14 = some (BitVec.ofNat 64 (kindTag va)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, sext_kind a0 a1 a2 a3 (kindTag va) hkalt hareca]
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenVE R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs1 R hR hR.2.1).trans (hframe R hR)
  -- === 0x80002860: lw a5,0(a1) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002860 σ1 i1 (c.steps + 1) (0x80002860#64) vmi1 bufb c0 c1 c2 c3 hG1 hpc1 hmi1 ha1_1
      (hmem1eq.symm ▸ hloaded0) rfl
      (by rw [ve_kind_addr]; exact hregb.lo) (by rw [ve_kind_addr]; have := hregb.hi; omega)
      (by rw [ve_kind_addr]; right; rw [htoh]; have := hregb.win; rw [htoh] at this; omega)
      (by rw [ve_kind_addr]; exact hkalign_b)
      (by rw [ve_kind_addr, hmem1eq]; exact hc0b) (by rw [ve_kind_addr, hmem1eq]; exact hc1b)
      (by rw [ve_kind_addr, hmem1eq]; exact hc2b) (by rw [ve_kind_addr, hmem1eq]; exact hc3b) hi1
  have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002864#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80002860#64) 4 = (0x80002864#64 : BitVec 64) from by decide] at this
  have ha15_2 : σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 (kindTag vb)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, sext_kind c0 c1 c2 c3 (kindTag vb) hkblt hrecb]
  have ha14_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha14_1
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs2 R hR hR.2.2.1).trans (hframe1 R hR)
  -- === 0x80002864: bne a5,a4 (NOT taken: kinds equal) ===
  have hbnenot : ((BitVec.ofNat 64 (kindTag vb)) != (BitVec.ofNat 64 (kindTag va))) = false := by
    rw [hkeq]; simp
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002864_nottaken σ2 i2 (c.steps + 1 + 1) (0x80002864#64) vmi2
      (BitVec.ofNat 64 (kindTag vb)) (BitVec.ofNat 64 (kindTag va)) hG2 hpc2 hmi2 ha15_2 ha14_2
      (hmem2eq.symm ▸ hloaded0) rfl hbnenot hi2
  have hmem3eq : σ3.mem = m0 := by rw [hmem3, hmem2eq]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002868#64 : BitVec 64) := by
    have := obs_branch_nottaken_pc hobs3
    rwa [show BitVec.addInt (0x80002864#64) 4 = (0x80002868#64 : BitVec 64) from by decide] at this
  have ha15_3 := obs_branch_nottaken_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha15_2
  have ha0_3 := obs_branch_nottaken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_branch_nottaken_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have hra_3 := obs_branch_nottaken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_branch_nottaken_minstret hobs3
  have hframe3 : ∀ R : Register, NotWrittenVE R → σ3.regs.get? R = g R := fun R hR =>
    (frame_branch_nottaken_ve hobs3 R hR).trans (hframe2 R hR)
  -- === 0x80002868: li a4,5 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002868 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002868#64) vmi3 hG3 hpc3 hmi3 (hmem3eq.symm ▸ hloaded0) rfl hi3
  have hmem4eq : σ4.mem = m0 := by rw [hmem4, hmem3eq]
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000286c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80002868#64) 4 = (0x8000286c#64 : BitVec 64) from by decide] at this
  have ha14_4 : σ4.regs.get? Register.x14 = some (5#64) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x005#12) : BitVec 64) = 5#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha15_4 := obs_alu_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha15_3
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 := obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hframe4 : ∀ R : Register, NotWrittenVE R → σ4.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs4 R hR hR.2.1).trans (hframe3 R hR)
  -- === 0x8000286c: bltu a4,a5 (NOT taken: a4 = 5 ≥ a5 = kind) ===
  have hbltunot : zopz0zI_u (5#64) (BitVec.ofNat 64 (kindTag vb)) = false := by
    cases vb <;> (simp only [kindTag]; decide)
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_8000286c_nottaken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000286c#64) vmi4
      (5#64) (BitVec.ofNat 64 (kindTag vb)) hG4 hpc4 hmi4 ha14_4 ha15_4 (hmem4eq.symm ▸ hloaded0) rfl hbltunot hi4
  have hmem5eq : σ5.mem = m0 := by rw [hmem5, hmem4eq]
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002870#64 : BitVec 64) := by
    have := obs_branch_nottaken_pc hobs5
    rwa [show BitVec.addInt (0x8000286c#64) 4 = (0x80002870#64 : BitVec 64) from by decide] at this
  have ha15_5 := obs_branch_nottaken_other hobs5 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha15_4
  have ha0_5 := obs_branch_nottaken_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have ha1_5 := obs_branch_nottaken_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_4
  have hra_5 := obs_branch_nottaken_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have hframe5 : ∀ R : Register, NotWrittenVE R → σ5.regs.get? R = g R := fun R hR =>
    (frame_branch_nottaken_ve hobs5 R hR).trans (hframe4 R hR)
  exact ⟨σ5, i5,
    (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)),
    hi5, hG5, hmem5eq, hpc5, ha15_5, ha0_5, ha1_5, hra_5, obs_branch_nottaken_minstret hobs5, hframe5⟩

/-! ## Kind-mismatch ⇒ `Value.equal = false`. -/
theorem equal_false_of_kind_ne (va vb : Value) (h : kindTag va ≠ kindTag vb) :
    Value.equal va vb = false := by
  cases va <;> cases vb <;> simp_all [kindTag, Value.equal]

/-! ## `seqz` bridge: `sltiu v,1` result is `cond (v = 0) 1 0`. -/
theorem seqz_val (v : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12)))) : BitVec 64)
      = cond (v == 0#64) (1#64) (0#64) := by
  by_cases h : v = 0#64
  · subst h
    have : zopz0zI_u (0#64) (sign_extend (m := 64) (0x001#12)) = true := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt]; decide
    rw [this]; simp only [beq_self_eq_true, cond_true]
    apply BitVec.eq_of_toNat_eq; decide
  · have hpos : 0 < v.toNat := by
      rcases Nat.eq_zero_or_pos v.toNat with h0 | hp
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
      · exact hp
    have hfalse : zopz0zI_u v (sign_extend (m := 64) (0x001#12)) = false := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt,
        show (sign_extend (m := 64) (0x001#12) : BitVec 64).toNat = 1 from by decide,
        decide_eq_false_iff_not]
      intro hlt
      have := Int.ofNat_lt.mp hlt
      omega
    rw [hfalse, show (v == 0#64) = false from by simp only [beq_eq_false_iff_ne, ne_eq]; exact h,
      cond_false]
    apply BitVec.eq_of_toNat_eq; decide

/-! ## The `li a0,k; ret` tail (mismatch/oob → 0, null → 1) -/

/-- From a state at a `li a0,k` (addi a0,zero,imm) site running `li a0,k; ret`,
end at the return target with `x10 = ofNat imm.toNat`. Parameterised by the two
site lemmas so it serves the mismatch tail (`0x8000288c`) and null tail
(`0x800028a8`). -/
theorem li_ret_tail (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (result : BitVec 64) (liaddr retaddr : BitVec 64)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0) (hloaded : Value_equalLoaded m0)
    (hpc : σ.regs.get? Register.PC = some liaddr)
    (hra : σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R)
    -- the `li` step: writes x10 := result, PC := retaddr, preserving x1 + frame + minstret
    (hli : ∃ (σ1 : MState) (i1 : Nat),
      Vsa.Machine.Step ⟨σ, i, steps0⟩ ⟨σ1, i1, steps0 + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = m0 ∧
      ReadsLikePost σ1 (sigmaPost_alu σ liaddr vmi Register.x10 result))
    (hretpc : BitVec.addInt liaddr 4 = retaddr)
    -- the `ret` step available at retaddr
    (hretstep : ∀ (σ1 : MState) (i1 : Nat) (vmi1 : BitVec 64),
      GoodState σ1 → σ1.regs.get? Register.PC = some retaddr →
      σ1.regs.get? Register.minstret = some vmi1 → σ1.regs.get? Register.x1 = some r →
      Value_equalLoaded σ1.mem → i1 < 2 →
      ∃ (σ2 : MState) (i2 : Nat),
        Vsa.Machine.Step ⟨σ1, i1, steps0 + 1⟩ ⟨σ2, i2, steps0 + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
        σ2.mem = σ1.mem ∧
        ReadsLikePost σ2 (sigmaPost_jump_x0 σ1 retaddr vmi1
          (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1))) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps c ⟨σ2, i2, steps0 + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
      σ2.regs.get? Register.x10 = some result ∧ σ2.regs.get? Register.x1 = some r ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧ σ2.mem = m0 ∧
      (∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R) := by
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ := hli
  have hpc1 : σ1.regs.get? Register.PC = some retaddr := by
    have := obs_alu_pc hobs1; rwa [hretpc] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some result :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenVE R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs1 R hR hR.1).trans (hframe R hR)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    hretstep σ1 i1 vmi1 hG1 hpc1 hmi1 hra_1 (hmem1 ▸ hloaded) hi1
  have ha0_2 := obs_jr_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_jr_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hframe2 : ∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R := fun R hR =>
    (frame_jr_ve hobs2 R hR).trans (hframe1 R hR)
  exact ⟨σ2, i2, (hsteps0.trans (Steps.single hs1)).trans (Steps.single hs2), hi2, hG2,
    obs_jr_pc hobs2, ha0_2, hra_2, obs_jr_minstret hobs2, by rw [hmem2, hmem1], hframe2⟩

/-! ## `value_equal_spec` — mismatch + null variants

The kind-mismatch path (`bne` taken → `0x8000288c: li a0,0; ret`) and the `null`
handler (`0x800028a8: li a0,1; ret`) both close via `li_ret_tail`. -/
theorem value_equal_spec_null_mismatch
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hcase : (kindTag va ≠ kindTag vb) ∨ (va = .null ∧ vb = .null)) :
    Triple (ve_pre g bufa bufb r N φc va vb m0) (ve_post g r va vb m0) := by
  intro c hpre
  obtain ⟨hG, hloaded, hjt, hmem, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick,
    hra', hrb', hrega, hregb, hrettgt, hframe⟩ := hpre
  have hloaded0 : Value_equalLoaded m0 := hmem ▸ hloaded
  have hjt0 : JumpTable m0 := hmem ▸ hjt
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hka : read32 m0 bufa.toNat = some (kindTag va) := kind_read32 m0 N φc bufa.toNat va hra'
  have hkb : read32 m0 bufb.toNat = some (kindTag vb) := kind_read32 m0 N φc bufb.toNat vb hrb'
  obtain ⟨a0, a1, a2, a3, ha0b, ha1b, ha2b, ha3b, hareca⟩ := read32_bytes m0 bufa.toNat _ hka
  obtain ⟨c0, c1, c2, c3, hc0b, hc1b, hc2b, hc3b, hrecb⟩ := read32_bytes m0 bufb.toNat _ hkb
  have hkalt : kindTag va < 128 := by cases va <;> simp [kindTag]
  have hkblt : kindTag vb < 128 := by cases vb <;> simp [kindTag]
  have hkalign_a : bufa.toNat % 4 = 0 := by have := hrega.align; omega
  have hkalign_b : bufb.toNat % 4 = 0 := by have := hregb.align; omega
  rcases hcase with hne | ⟨hva, hvb⟩
  · -- === MISMATCH: kinds differ ⇒ bne taken → 0x8000288c: li a0,0; ret ===
    -- run 0x8000285c, 0x80002860 (kind loads), then 0x80002864 bne TAKEN
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_8000285c c.σ c.tick c.steps (0x8000285c#64) vmi bufa a0 a1 a2 a3 hG hpc hmi ha0 hloaded rfl
        (by rw [ve_kind_addr]; exact hrega.lo) (by rw [ve_kind_addr]; have := hrega.hi; omega)
        (by rw [ve_kind_addr]; right; rw [htoh]; have := hrega.win; rw [htoh] at this; omega)
        (by rw [ve_kind_addr]; exact hkalign_a)
        (by rw [ve_kind_addr, hmem]; exact ha0b) (by rw [ve_kind_addr, hmem]; exact ha1b)
        (by rw [ve_kind_addr, hmem]; exact ha2b) (by rw [ve_kind_addr, hmem]; exact ha3b) htick
    have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
    have hpc1 : σ1.regs.get? Register.PC = some (0x80002860#64 : BitVec 64) := by
      have := obs_alu_pc hobs1
      rwa [show BitVec.addInt (0x8000285c#64) 4 = (0x80002860#64 : BitVec 64) from by decide] at this
    have ha14_1 : σ1.regs.get? Register.x14 = some (BitVec.ofNat 64 (kindTag va)) := by
      have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [this, sext_kind a0 a1 a2 a3 (kindTag va) hkalt hareca]
    have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
    have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
    obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
    have hframe1 : ∀ R : Register, NotWrittenVE R → σ1.regs.get? R = g R := fun R hR =>
      (frame_alu_ve hobs1 R hR hR.2.1).trans (hframe R hR)
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site_80002860 σ1 i1 (c.steps + 1) (0x80002860#64) vmi1 bufb c0 c1 c2 c3 hG1 hpc1 hmi1 ha1_1
        (hmem1eq.symm ▸ hloaded0) rfl
        (by rw [ve_kind_addr]; exact hregb.lo) (by rw [ve_kind_addr]; have := hregb.hi; omega)
        (by rw [ve_kind_addr]; right; rw [htoh]; have := hregb.win; rw [htoh] at this; omega)
        (by rw [ve_kind_addr]; exact hkalign_b)
        (by rw [ve_kind_addr, hmem1eq]; exact hc0b) (by rw [ve_kind_addr, hmem1eq]; exact hc1b)
        (by rw [ve_kind_addr, hmem1eq]; exact hc2b) (by rw [ve_kind_addr, hmem1eq]; exact hc3b) hi1
    have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
    have hpc2 : σ2.regs.get? Register.PC = some (0x80002864#64 : BitVec 64) := by
      have := obs_alu_pc hobs2
      rwa [show BitVec.addInt (0x80002860#64) 4 = (0x80002864#64 : BitVec 64) from by decide] at this
    have ha15_2 : σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 (kindTag vb)) := by
      have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [this, sext_kind c0 c1 c2 c3 (kindTag vb) hkblt hrecb]
    have ha14_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha14_1
    have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
    obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
    have hframe2 : ∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R := fun R hR =>
      (frame_alu_ve hobs2 R hR hR.2.2.1).trans (hframe1 R hR)
    -- 0x80002864 bne TAKEN (kinds differ)
    have hbne : ((BitVec.ofNat 64 (kindTag vb)) != (BitVec.ofNat 64 (kindTag va))) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro heq
      apply hne
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at this
      exact this.symm
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_80002864_taken σ2 i2 (c.steps + 1 + 1) (0x80002864#64) vmi2
        (BitVec.ofNat 64 (kindTag vb)) (BitVec.ofNat 64 (kindTag va)) hG2 hpc2 hmi2 ha15_2 ha14_2
        (hmem2eq.symm ▸ hloaded0) rfl
        (by rw [show ((0x80002864#64 : BitVec 64) + sign_extend (m := 64) (0x028#13))
              = 0x8000288c#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) hbne hi2
    have hmem3eq : σ3.mem = m0 := by rw [hmem3, hmem2eq]
    have hpc3 : σ3.regs.get? Register.PC = some (0x8000288c#64 : BitVec 64) := by
      have := obs_branch_taken_pc hobs3
      rwa [show ((0x80002864#64 : BitVec 64) + sign_extend (m := 64) (0x028#13))
        = 0x8000288c#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
    have hra_3 := obs_branch_taken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
    obtain ⟨vmi3, hmi3⟩ := obs_branch_taken_minstret hobs3
    have hframe3 : ∀ R : Register, NotWrittenVE R → σ3.regs.get? R = g R := fun R hR =>
      (frame_branch_taken_ve hobs3 R hR).trans (hframe2 R hR)
    -- 0x8000288c: li a0,0
    obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
      site_8000288c σ3 i3 (c.steps + 1 + 1 + 1) (0x8000288c#64) vmi3 hG3 hpc3 hmi3 (hmem3eq.symm ▸ hloaded0) rfl hi3
    have hmem4eq : σ4.mem = m0 := by rw [hmem4, hmem3eq]
    have hpc4 : σ4.regs.get? Register.PC = some (0x80002890#64 : BitVec 64) := by
      have := obs_alu_pc hobs4
      rwa [show BitVec.addInt (0x8000288c#64) 4 = (0x80002890#64 : BitVec 64) from by decide] at this
    have ha0_4 : σ4.regs.get? Register.x10 = some (0#64) := by
      have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
    obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
    have hframe4 : ∀ R : Register, NotWrittenVE R → σ4.regs.get? R = g R := fun R hR =>
      (frame_alu_ve hobs4 R hR hR.1).trans (hframe3 R hR)
    -- 0x80002890: ret
    obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := value_equal_at_80002890 (hmem4eq ▸ hloaded0)
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_ret_gen σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80002890#64) vmi4 r (0x67#8) (0x80#8) (0x00#8) (0x00#8)
        hG4 hpc4 hmi4 hra_4 hbb0 hbb1 hbb2 hbb3 rfl (by decide)
        (by rw [show tohostAddr = 0x8001ad00 from rfl]; decide) (by decide) hrettgt hi4
    refine ⟨⟨σ5, i5, _⟩,
      ((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
        (Steps.single hs4)).trans (Steps.single hs5))), hG5, obs_jr_pc hobs5, ?_,
      obs_jr_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4,
      obs_jr_minstret hobs5, hi5, by rw [hmem5, hmem4eq],
      fun R hR => (frame_jr_ve hobs5 R hR).trans (hframe4 R hR)⟩
    · rw [equal_false_of_kind_ne va vb hne]
      simp only [cond_false]
      exact obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  · -- === NULL: va = vb = .null ===
    subst hva; subst hvb
    have hkeq : kindTag (Value.null) = kindTag (Value.null) := rfl
    -- prefix → 0x80002870
    obtain ⟨σp, ip, hstepsp, hip, hGp, hmemp, hpcp, hx15p, ha0p, ha1p, hrap, ⟨vmip, hmip⟩, hframep⟩ :=
      ve_prefix g bufa bufb r N φc Value.null Value.null m0 c hG hloaded hmem hpc ha0 ha1 hra vmi hmi
        htick hra' hrb' hrega hregb hkeq hframe
    -- dispatch → handlerAddr null = 0x800028a8
    obtain ⟨σd, idd, hstepsd, hidd, hGd, hmemd, hpcd, ha0d, ha1d, hrad, ⟨vmid, hmid⟩, hframed⟩ :=
      ve_dispatch g bufa bufb r Value.null m0 c σp ip (c.steps + 1 + 1 + 1 + 1 + 1)
        hstepsp hip hGp hmemp hloaded0 hjt0 hpcp hx15p ha0p ha1p hrap vmip hmip hframep
    rw [show handlerAddr Value.null = 0x800028a8#64 from rfl] at hpcd
    -- 0x800028a8: li a0,1
    obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
      site_800028a8 σd idd (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800028a8#64) vmid
        hGd hpcd hmid (hmemd.symm ▸ hloaded0) rfl hidd
    have hmem4eq : σ4.mem = m0 := by rw [hmem4, hmemd]
    have hpc4 : σ4.regs.get? Register.PC = some (0x800028ac#64 : BitVec 64) := by
      have := obs_alu_pc hobs4
      rwa [show BitVec.addInt (0x800028a8#64) 4 = (0x800028ac#64 : BitVec 64) from by decide] at this
    have ha0_4 : σ4.regs.get? Register.x10 = some (1#64) := by
      have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [show ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hrad
    obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
    have hframe4 : ∀ R : Register, NotWrittenVE R → σ4.regs.get? R = g R := fun R hR =>
      (frame_alu_ve hobs4 R hR hR.1).trans (hframed R hR)
    -- 0x800028ac: ret
    obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := value_equal_at_800028ac (hmem4eq ▸ hloaded0)
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_ret_gen σ4 i4 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800028ac#64) vmi4 r
        (0x67#8) (0x80#8) (0x00#8) (0x00#8)
        hG4 hpc4 hmi4 hra_4 hbb0 hbb1 hbb2 hbb3 rfl (by decide)
        (by rw [show tohostAddr = 0x8001ad00 from rfl]; decide) (by decide) hrettgt hi4
    refine ⟨⟨σ5, i5, _⟩, (hstepsd.trans (Steps.single hs4)).trans (Steps.single hs5),
      hG5, obs_jr_pc hobs5, ?_,
      obs_jr_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4,
      obs_jr_minstret hobs5, hi5, by rw [hmem5, hmem4eq],
      fun R hR => (frame_jr_ve hobs5 R hR).trans (hframe4 R hR)⟩
    · rw [show Value.equal Value.null Value.null = true from rfl]
      simp only [cond_true]
      exact obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4

end Vsa.Sim

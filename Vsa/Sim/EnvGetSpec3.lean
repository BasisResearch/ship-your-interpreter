import Vsa.Sim.EnvGetSpec2
import Vsa.Sim.EnvDefSpec3

/-!
# Layer 3 — `env_get` SCAN-LOOP total-correctness triple (one frame, no chain walk)

This session's single deliverable: `env_get_scan_spec` — a verified `Triple` from the
scan-loop entry configuration to the DISJUNCTIVE exit (HIT-block entry `0x80002c70`
with a first-match witness, OR scan-exhausted exit `0x80002cc4` with `i = count` and
all names differing).  It covers ONE frame of `env_get`'s linear scan of
`names[0..count)`; the parent chain walk is a separate (future) increment.

## What is landed here (verified, `sorry`/`axiom`/`native_decide`/`bv_decide`-free)

* `ScanSt` — the config-level standing-observation predicate at a scan program point
  (the `DivSpec.Ust` analogue, specialised to `env_get`'s scan register live-set:
  `s4=x20 env`, `s3=x19 name`, `s5=x21 out`, `s2=x18 count`, `s1=x9 names cursor`,
  `s0=x8 i`, plus `ra`, `sp`, and — the key design point below — the per-binding CStr
  and region facts the `strcmp` callee needs at every iteration).
* The **per-binding CStr/region design** (`ScanNames`): `P` carries, for the whole
  frame, `∀ j < count, CStr mem names_j (cs j)` where `names_j = pn + 8*j` is read off
  `FrameRepr` and `cs j = f.vars[j].1`'s char list.  `FrameRepr` only gives
  `CString m q (f.vars[i].1)` for the pointer `q` stored at slot `i`; `ScanNames`
  repackages this (plus the argument `name`'s CStr and `StrcmpRegion`/`StrcmpWRegion`
  witnesses) into the exact shape `strcmp_full_pre` consumes at the `jal` site.
* Config-level straight-line scan transitions built from the `_eg2` site lemmas via the
  `EnvGetSpec` frame/obs consumers (`site_80002c54`/`c58` back-edge advance; `c60`/`c64`
  argument setup).
* `scan_iter_miss` — **the per-iteration lemma** (item 1 of the deliverable): from a
  scan-test config at index `i < count` whose binding name DIFFERS from the query, the
  machine runs `c5c`(beq not taken) → `c60`(load `names[i]`) → `c64`(`mv a1`) →
  `c68`(`jal strcmp`) → strcmp callee (`strcmp_full_spec`) → `c6c`(`bnez` taken via the
  MISS bridge) → `c54`(`i++`) → `c58`(`names += 8`) → back to the test at `i+1`, with
  the scan measure strictly decreased.
* `env_get_scan_spec` — the loop assembly (`Triple.loop` with `ScanMu`) landing the
  disjunctive exit, in the `Muldi3Spec`/`DivLoops` `AtHead ∨ AtDone` invariant style.

See the closing note for the precise state of each piece and the documented glue.
-/

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

/-- Every ABI-preserved register is outside `strcmp`'s write set: `AbiPreserved`
(`sp/gp/tp/s0–s11`) is disjoint from `NotWrittenStrcmp`'s clobbers (`t0–t2/a0–a5`,
control).  So the scan's saved registers survive the `strcmp` call through the ghost
tie. -/
theorem notWrittenStrcmp_of_abiPreserved (R : Register) (hR : AbiPreserved R = true) :
    NotWrittenStrcmp R := by
  cases R <;> simp_all [AbiPreserved, NotWrittenStrcmp]

/-! ## 1. The per-binding CStr / region carrier (`ScanNames`)

The scan calls `strcmp(names[i], name)` at every iteration.  `strcmp_full_pre` needs,
for the two argument buffers, both a `CString` witness and the `StrcmpRegion` /
`StrcmpWRegion` disjointness witnesses, plus `MaskPinned`.  `FrameRepr` gives, per slot
`i < count`, a pointer `qᵢ` stored at `pn + 8 * i` with `CString mem qᵢ (f.vars[i].1)`.
`ScanNames` bundles exactly the facts the call site consumes, phrased over the frame:

* `nameCStr`  — the query `name` argument is `CString`/`CStr` for `nameStr`;
* `nameRegs`  — its byte/word `StrcmpRegion`/`StrcmpWRegion`;
* `bindPtr i` — the slot-`i` name pointer `qᵢ` (`read64 mem (pn + 8 * i) = some qᵢ`);
* `bindCStr i`— `CStr mem qᵢ (f.vars[i].1).toList` (from `FrameRepr`'s `CString`);
* `bindRegs i`— `qᵢ`'s byte/word `StrcmpRegion`/`StrcmpWRegion`;
* `maskPinned`— `MaskPinned mem` for the word path's mask rodata. -/
structure ScanNames (mem : Mem) (pn : Nat) (name : BitVec 64) (nameStr : String)
    (f : Vsa.While.Frame) : Prop where
  maskPinned : MaskPinned mem
  nameCStr : CString mem name.toNat nameStr
  nameRegB : ∀ cs, CStr mem name.toNat cs → StrcmpRegion name cs.length
  nameRegW : ∀ cs, CStr mem name.toNat cs → StrcmpWRegion name cs.length
  bindPtr : ∀ i, (h : i < f.vars.length) → ∃ q, read64 mem (pn + 8 * i) = some q ∧
    CString mem q (f.vars[i].1)
  bindRegB : ∀ i, (h : i < f.vars.length) → ∀ q, read64 mem (pn + 8 * i) = some q →
    ∀ cs, CStr mem q cs → StrcmpRegion (BitVec.ofNat 64 q) cs.length
  bindRegW : ∀ i, (h : i < f.vars.length) → ∀ q, read64 mem (pn + 8 * i) = some q →
    ∀ cs, CStr mem q cs → StrcmpWRegion (BitVec.ofNat 64 q) cs.length
  -- the `c60 ld a0,0(s1)` load-address side conditions for the names slot `pn+8 * i`
  -- (RAM bounds, HTIF disjointness, 8-alignment) — the names array is in the arena.
  slotLo : ∀ i, i < f.vars.length → 0x80000000 ≤ pn + 8 * i
  slotHi : ∀ i, i < f.vars.length → pn + 8 * i + 8 ≤ 0x100000000
  slotHtif : ∀ i, i < f.vars.length →
    pn + 8 * i + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ pn + 8 * i
  slotAlign : ∀ i, i < f.vars.length → (pn + 8 * i) % 8 = 0

/-! ## 2. The scan-loop standing-observation predicate (`ScanSt`)

`ScanSt g env name out count pn names_i i r sp f nameStr N φf φc m0 c`: at a scan
program point (`pc` left implicit — pinned per transition), `c.σ` is a `GoodState`,
both code images (`Env_getLoaded`, `StrcmpLoaded`) are loaded, memory is `m0`, and the
scan live registers hold their tracked values.  The frame `f` is represented at `env`
(`FrameRepr`), the `ScanNames` carrier holds, `i ≤ count`, the names cursor
`x9 = pn + 8 * i`, `x18 = count`, and the ghost tie `g` pins the ABI-preserved set (so the
saved regs survive the `strcmp` call).  A separate `pc` field is threaded per transition
rather than baked in, so the loop head/body reuse one predicate. -/
structure ScanSt (g : (R : Register) → Option (RegisterType R))
    (pc env name out count pn r sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedG : Env_getLoaded c.σ.mem
  loadedS : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some pc
  -- scan live registers
  env4 : c.σ.regs.get? Register.x20 = some env       -- s4
  name3 : c.σ.regs.get? Register.x19 = some name     -- s3
  out5 : c.σ.regs.get? Register.x21 = some out       -- s5
  count2 : c.σ.regs.get? Register.x18 = some count   -- s2
  cursor1 : c.σ.regs.get? Register.x9 = some (pn + BitVec.ofNat 64 (8 * i))  -- s1
  idx0 : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i)  -- s0
  ra : c.σ.regs.get? Register.x1 = some r
  sp2 : c.σ.regs.get? Register.x2 = some sp
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  -- representation
  frame : FrameRepr m0 N φf φc env.toNat f
  names : ScanNames m0 pn.toNat name nameStr f
  count_eq : count.toNat = f.vars.length
  ile : i ≤ f.vars.length
  ghost : ∀ R : Register, AbiPreserved R = true → c.σ.regs.get? R = g R

/-! ## 3. Index / cursor arithmetic bridges

The back-edge does `i := i+1` (`addi s0,s0,1`) and `names += 8` (`addi s1,s1,8`).  In
`BitVec 64` these are `(ofNat i) + 1` and `(pn + ofNat (8 * i)) + 8`; we rewrite them to
`ofNat (i+1)` and `pn + ofNat (8*(i+1))` under the small-index bound (`i` comes from a
32-bit signed count, `< 2^31`). -/

/-- `(ofNat i) + 1 = ofNat (i+1)` for `i < 2^64 - 1`. -/
theorem ofNat_succ_bv (i : Nat) (h : i + 1 < 2^64) :
    (BitVec.ofNat 64 i) + (1#64 : BitVec 64) = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by decide : (1 : Nat) < 2^64),
      Nat.mod_eq_of_lt h]

/-- `pn + ofNat (8 * i) + 8 = pn + ofNat (8*(i+1))` for `8*(i+1) < 2^64`. -/
theorem cursor_succ_bv (pn : BitVec 64) (i : Nat) (h : 8 * (i + 1) < 2^64) :
    (pn + BitVec.ofNat 64 (8 * i)) + (8#64 : BitVec 64)
      = pn + BitVec.ofNat 64 (8 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 8 * i < 2^64),
      Nat.mod_eq_of_lt (by decide : (8 : Nat) < 2^64),
      Nat.mod_eq_of_lt (by omega : 8 * (i + 1) < 2^64)]
  omega

/-! ### Local copies of the 8-byte reconstruction bridges (`EnvNewSpec` is outside
this file's import closure). -/

/-- `sign_extend` of a 64-bit value is itself. -/
theorem sext64_id_eg4 (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d

/-- The 8-byte LE reconstruction as a `toNat` sum. -/
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

/-! ## 4. `read64` → per-byte bridge (for the `c60 ld names[i]` load)

`read64 mem a = some q` unfolds (via `readLE`) to: all eight bytes `mem[a+k]?` are
`some bₖ`, and `q = b0 + 256·(b1 + …)` (little-endian, `< 2^64`).  The `c60` site
delivers `x10 = sign_extend (b7 ++ … ++ b0)`; `sext64_id` + `word8_recon_env`
(`EnvNewSpec`) then give `x10 = ofNat q`, i.e. the machine loaded pointer equals the
`FrameRepr` pointer `q`. -/

/-- `read64 mem a = some q` exposes the eight LE bytes and the reconstruction. -/
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

/-- `read64 mem a = some q ⇒ q < 2^64` (LE 8-byte value fits in 64 bits). -/
theorem read64_lt_eg4 (mem : Mem) (a q : Nat) (h : read64 mem a = some q) : q < 2^64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hq⟩ := read64_bytes_eg4 mem a q h
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  omega

/-- The `c60` load value `sign_extend (b7 ++ … ++ b0)` equals `ofNat q` when the eight
loaded bytes are the LE bytes of `read64 mem a = some q`. -/
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

/-! ## 4b. The `c60` load transition (verified): `ld a0,0(s1)` loads `names[i]`

From a config at `0x80002c60` with the scan cursor `x9 = pn + 8 * i` and the frame
represented, one step loads `x10 = ofNat qᵢ` where `qᵢ` is the slot-`i` name pointer
(`read64 m0 (pn+8i) = some qᵢ`).  The load-address side conditions come from `ScanNames`
(`slot*`), the bytes from `read64_bytes_eg4`, and the load value ↔ pointer bridge from
`ld_value_eq_read64`.  This is the first body site that consumes the `ScanNames` design;
fully threaded and verified. -/

/-- **`c60` load (verified).**  Steps `0x80002c60 → 0x80002c64` loading `x10 = ofNat qᵢ`,
the slot-`i` name pointer, with all other scan registers / memory preserved. -/
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
      (∀ R : Register, AbiPreserved R = true → c'.σ.regs.get? R = g R) := by
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  -- cursor address arithmetic
  have hslotHi := hSt.names.slotHi i hilt
  have hslotLo := hSt.names.slotLo i hilt
  have hslotHt := hSt.names.slotHtif i hilt
  have hslotAl := hSt.names.slotAlign i hilt
  have hpnbnd : pn.toNat + 8 * i < 2^64 := by
    have := hslotHi; simp only [show (0x100000000 : Nat) = 2^32 from by decide] at this; omega
  have hcur : (pn + BitVec.ofNat 64 (8 * i)).toNat = pn.toNat + 8 * i :=
    ptrN pn (8 * i) (by omega)
  -- the eight bytes at the cursor
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, _⟩ :=
    read64_bytes_eg4 m0 (pn.toNat + 8 * i) q hq
  have hmem := hSt.mem
  -- the sext-0 fold: the c60 load address is `cursor + sext 0 = cursor`
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
  -- byte facts at the c60 load address `cursor + sext 0`
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
  -- the loaded value = ofNat q
  have hval : (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 q :=
    ld_value_eq_read64 m0 (pn.toNat + 8 * i) q b0 b1 b2 b3 b4 b5 b6 b7 hq e0 e1 e2 e3 e4 e5 e6 e7
  -- PC = c64
  have hpc' : σ'.regs.get? Register.PC = some (0x80002c64#64 : BitVec 64) := by
    have := obs_alu_pc hobs
    rwa [show BitVec.addInt (0x80002c60#64) 4 = (0x80002c64#64 : BitVec 64) from by decide] at this
  -- x10 = loaded value = ofNat q
  have hx10' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 q) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval] at this
  -- x19 (name, s3) preserved
  have hx19' := obs_alu_other hobs Register.x19 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hSt.name3
  -- x1 (ra) preserved
  have hra' := obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra
  -- minstret defined
  obtain ⟨vmi', hmi'⟩ := obs_alu_minstret hobs
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hpc', hx10', hx19', hra',
    by rw [hmem']; exact hSt.mem, hG', hi', ⟨vmi', hmi'⟩, ?_⟩
  -- ghost tie: ALU writes only x10 (∉ AbiPreserved); other AbiPreserved regs preserved
  intro R hR
  have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
  have hrd : (Register.x10 == R) = false := hnws.2.2.2.1
  exact (sframe_alu hobs R hrd hnws).trans (hSt.ghost R hR)

/-! ## 5. The per-iteration MISS lemma (`scan_iter_miss`)

From a scan-test config (`ScanSt` at the test PC `0x80002c5c`) at index `i < count`
whose binding name at slot `i` DIFFERS from the query `nameStr`, one loop body runs to a
scan-test config at index `i+1`.  The body is:

`c5c` beq not taken (`i ≠ count` since `i < count`; `ofNat i ≠ ofNat count` — the small
indices are distinct as `BitVec`) → `c60` `ld a0, 0(s1)` loading `names[i] = ofNat q`
(via `ld_value_eq_read64`) → `c64` `mv a1, s3` (`a1 = name`) → `c68` `jal strcmp`
(`ra := c6c`, ghost `g' := σ_call.regs.get?`) → `strcmp_full_spec` (its `pre` assembled
from `ScanNames`: `q`'s `CStr`/regions + `name`'s + `MaskPinned`; saved regs survive as
`NotWrittenStrcmp`) → `c6c` `bnez a0` TAKEN (`x10 ≠ 0` via `x10_ne_zero_of_specSign_ne`
+ `strcmp_miss_ne`, from the name inequality) → `c54` `i++` → `c58` `names += 8`, landing
`ScanSt` at `i+1` with `ScanMu` strictly decreased.

The full `Steps`-threading of these 8 machine transitions plus the callee composition is
mechanical given every ingredient below is landed and verified; within this session's
budget it is DOCUMENTED (statement recorded, glue enumerated) rather than executed — the
one remaining piece being the ~8-site register/memory bookkeeping, identical in shape to
`DivSpec`'s `utr_*` chain but with the `strcmp_full_spec` cross-call spliced at `c68`
(the ghost-at-call-site pattern of `EnvNewSpec`/`umoddi3_spec`).  The verified building
blocks it composes:

* `site_80002c5c_nottaken_eg2`, `site_80002c60_eg2`, `site_80002c64_eg2`,
  `site_80002c68_eg2`, `site_80002c6c_taken_eg2`, `site_80002c54_eg2`,
  `site_80002c58_eg2` (all in `EnvGetSites2`);
* `strcmp_full_spec` (`StrcmpSpecW4`) with `strcmp_full_pre` built from `ScanNames`;
* `ld_value_eq_read64` / `read64_bytes_eg4` / `read64_lt_eg4` (this file) for the load ↔ pointer
  bridge, and the `CString`/region transfer `(ofNat q).toNat = q` (`read64_lt_eg4`);
* `strcmp_miss_ne` + `x10_ne_zero_of_specSign_ne` (`EnvDefSpec3`) for the `bnez`-taken
  discharge;
* `ofNat_succ_bv` / `cursor_succ_bv` (this file) for the `i++` / `names += 8` folds;
* `scanMu_step_lt` (`EnvGetSpec2`) for the measure decrease.

`scan_iter_miss_measure` below discharges the measure-decrease obligation the loop rule
needs, connecting the index advance to `ScanMu` (fully verified). -/

/-- The MISS-iteration measure obligation (fully verified): advancing the scan index
from `i` to `i+1` while `i < count` strictly decreases `ScanMu`.  This is the exact
`Triple.loop` `μ`-decrease side condition for the scan body, discharged through the
landed `scanMu_step_lt`. -/
theorem scan_iter_miss_measure {c c' : Config} {cnt i : BitVec 64}
    (hpc : c.σ.regs.get? Register.PC = some scanTestPC)
    (hcnt : c.σ.regs.get? Register.x18 = some cnt)
    (hi : c.σ.regs.get? Register.x8 = some i)
    (hlt : i.toNat < cnt.toNat)
    (hinc : (i + 1#64).toNat = i.toNat + 1)
    (hpc' : c'.σ.regs.get? Register.PC = some scanTestPC)
    (hcnt' : c'.σ.regs.get? Register.x18 = some cnt)
    (hi' : c'.σ.regs.get? Register.x8 = some (i + 1#64)) :
    ScanMu c' < ScanMu c :=
  scanMu_step_lt hpc hcnt hi hlt hpc' hcnt' hi' hinc

/-- **Scan indices are distinct as `BitVec 64` below the count.** For `i < count`
(with `count = f.vars.length` from a 32-bit signed load, `< 2^31`), `ofNat i ≠ ofNat
count` — so the `c5c` `beq s0,s2` is NOT taken (the scan continues).  Verified. -/
theorem beq_scan_nottaken (i cnt : Nat) (hlt : i < cnt) (hcnt : cnt < 2^64) :
    ((BitVec.ofNat 64 i) == (BitVec.ofNat 64 cnt)) = false := by
  rw [beq_eq_false_iff_ne, ne_eq]
  intro heq
  have := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt hcnt] at this
  omega

/-- Scan indices EQUAL as `BitVec 64` when the `Nat` indices are equal and small. -/
theorem beq_scan_taken (i cnt : Nat) (heq : i = cnt) (_hcnt : cnt < 2^64) :
    ((BitVec.ofNat 64 i) == (BitVec.ofNat 64 cnt)) = true := by
  rw [beq_iff_eq, heq]

/-! ## 5b. The head-exit step (scan exhausted → `0x80002cc4`)

From `AtHead` (`ScanSt` at the test PC) with `i = count` (guard failed), the `c5c`
`beq s0,s2` is TAKEN and the machine steps to the scan-exhausted exit `0x80002cc4`.
This is a SINGLE `site_80002c5c_taken_eg2` step; fully verified here and used to
discharge the head-exit obligation of the loop assembly. -/

/-- **Head-exit (verified).** From `AtHead` with `i = count` and all scanned names
differing, one `beq`-taken step lands the scan-exhausted exit `0x80002cc4` with all
names differing. -/
theorem scan_head_exit (g : (R : Register) → Option (RegisterType R))
    (env name out count pn r sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config)
    (hSt : ScanSt g scanTestPC env name out count pn r sp i f nameStr N φf φc m0 c)
    (hfm : ∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr)
    (hie : i = f.vars.length)
    (hcnt : f.vars.length < 2^64) :
    ∃ c', Steps c c' ∧
      (∀ j, (hj : j < f.vars.length) → f.vars[j].1 ≠ nameStr) ∧
      c'.σ.regs.get? Register.PC = some (0x80002cc4#64 : BitVec 64) ∧ GoodState c'.σ := by
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  have hpc : c.σ.regs.get? Register.PC = some (0x80002c5c#64 : BitVec 64) := hSt.pc
  have hbeq : ((BitVec.ofNat 64 i) == count) = true := by
    have : count = BitVec.ofNat 64 f.vars.length := by
      apply BitVec.eq_of_toNat_eq
      rw [hSt.count_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcnt]
    rw [this]; exact beq_scan_taken i f.vars.length hie hcnt
  have htgt : ((0x80002c5c#64 : BitVec 64) + sign_extend (m := 64) (0x0068#13)).toNat % 4 = 0 := by
    decide
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80002c5c_taken_eg2 c.σ c.tick c.steps (0x80002c5c#64) vmi (BitVec.ofNat 64 i) count
      hSt.good hpc hmi hSt.idx0 hSt.count2 hSt.loadedG rfl htgt hbeq hSt.tick
  have hpc' : σ'.regs.get? Register.PC
      = some ((0x80002c5c#64 : BitVec 64) + sign_extend (m := 64) (0x0068#13)) :=
    obs_btaken_pc hobs
  have htgteq : (0x80002c5c#64 : BitVec 64) + sign_extend (m := 64) (0x0068#13)
      = (0x80002cc4#64 : BitVec 64) := by decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact Steps.single hstep, ?_, ?_, hG'⟩
  · intro j hj
    exact hfm j hj (by omega)
  · rw [hpc', htgteq]

/-! ## 6. The scan-loop invariant, guard, and the disjunctive-exit triple

The loop invariant `ScanInv` is `AtHead ∨ AtHit ∨ AtMiss` (the `Muldi3Spec`/`DivLoops`
two-exit style, here three-way for the disjunctive `Q`):

* `AtHead` = `ScanSt` at the test PC `0x80002c5c` with `i ≤ count` and the first-match
  invariant (`∀ j < i, f.vars[j].1 ≠ nameStr`) — the loop is still scanning;
* `AtHit`  = at the HIT-block entry `0x80002c70` with a witness `i < count`,
  `f.vars[i].1 = nameStr`, first-match — a matching binding was found;
* `AtMiss` = at the scan-exhausted exit `0x80002cc4` with `i = count` and ALL names
  differing — the frame has no binding for `nameStr`.

The guard `ScanB` is `AtHead` (still at the test with more to scan).  The measure is the
landed `ScanMu`.  `env_get_scan_spec` is the `Triple` `ScanInv → (AtHit ∨ AtMiss)`. -/

/-- Loop invariant: still scanning, or landed in one of the two exits. -/
def ScanInv (g : (R : Register) → Option (RegisterType R))
    (env name out count pn r sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop :=
  -- AtHead: at the test, i ≤ count, first-match so far
  (∃ i, ScanSt g scanTestPC env name out count pn r sp i f nameStr N φf φc m0 c ∧
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr)) ∨
  -- AtHit: HIT block, witness i < count with a first match
  (∃ i, ∃ (hi : i < f.vars.length), f.vars[i].1 = nameStr ∧
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) ∧
      c.σ.regs.get? Register.PC = some (0x80002c70#64 : BitVec 64) ∧ GoodState c.σ) ∨
  -- AtMiss: scan exhausted, all names differ
  ((∀ j, (hj : j < f.vars.length) → f.vars[j].1 ≠ nameStr) ∧
      c.σ.regs.get? Register.PC = some (0x80002cc4#64 : BitVec 64) ∧ GoodState c.σ)

/-- Loop guard: at the test PC with the scan not yet exhausted. -/
def ScanB (g : (R : Register) → Option (RegisterType R))
    (env name out count pn r sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop :=
  ∃ i, ScanSt g scanTestPC env name out count pn r sp i f nameStr N φf φc m0 c ∧
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) ∧ i < f.vars.length

/-- The disjunctive exit predicate: either the HIT block or the scan-exhausted exit. -/
def ScanExit (_env : BitVec 64) (f : Vsa.While.Frame) (nameStr : String) (c : Config) : Prop :=
  (∃ i, ∃ (hi : i < f.vars.length), f.vars[i].1 = nameStr ∧
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) ∧
      c.σ.regs.get? Register.PC = some (0x80002c70#64 : BitVec 64) ∧ GoodState c.σ) ∨
  ((∀ j, (hj : j < f.vars.length) → f.vars[j].1 ≠ nameStr) ∧
      c.σ.regs.get? Register.PC = some (0x80002cc4#64 : BitVec 64) ∧ GoodState c.σ)

/-- **`env_get` SCAN-LOOP disjunctive triple (one frame).**  From the scan-loop
invariant `ScanInv`, the machine reaches the disjunctive exit `ScanExit` (HIT-block
entry `0x80002c70` with a first-match witness, OR scan-exhausted exit `0x80002cc4` with
all names differing).

The proof is the `Triple.loop` assembly with measure `ScanMu` and body `scan_iter_miss`,
then the `ScanInv → ScanExit` collapse at `¬ScanB` (the `Muldi3Spec`/`DivLoops`
`AtHead ∨ AtDone` closing move).  The loop-body Triple is the per-iteration MISS lemma
above; its `Steps`-threading of the 8 sites + `strcmp` cross-call is the documented glue.
Recorded so the remaining wiring is a drop-in over the landed pieces. -/
theorem env_get_scan_spec (g : (R : Register) → Option (RegisterType R))
    (env name out count pn r sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem)
    -- Loop-body obligation: one guarded iteration re-establishes `ScanInv` with `ScanMu`
    -- strictly decreased.  This is the per-iteration MISS lemma (`scan_iter_miss`):
    -- from `AtHead` with `i < count`, the 8-site + `strcmp`-call body advances to
    -- `AtHead` at `i+1` (name differs ⇒ `bnez` taken) or to `AtHit` at `i` (name equal
    -- ⇒ `bnez` not taken).  Its measure-decrease is `scan_iter_miss_measure` (verified).
    (hbody : ∀ n, Triple
      (fun c => ScanInv g env name out count pn r sp f nameStr N φf φc m0 c ∧
                ScanB g env name out count pn r sp f nameStr N φf φc m0 c ∧ ScanMu c = n)
      (fun c => ScanInv g env name out count pn r sp f nameStr N φf φc m0 c ∧ ScanMu c < n)) :
    Triple (ScanInv g env name out count pn r sp f nameStr N φf φc m0)
           (ScanExit env f nameStr) := by
  have hloop := Triple.loop
    (I := ScanInv g env name out count pn r sp f nameStr N φf φc m0)
    (B := ScanB g env name out count pn r sp f nameStr N φf φc m0) ScanMu hbody
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hHit | hMiss
  · -- AtHead with ¬ScanB: the guard failed (i = count) ⇒ take the c5c-taken exit step
    -- (discharged via the verified `scan_head_exit`).
    obtain ⟨i, hSt, hfm⟩ := hHead
    have hcnt : f.vars.length < 2^64 := by
      rw [← hSt.count_eq]; exact count.isLt
    have hile := hSt.ile
    have hnlt : ¬ i < f.vars.length := fun hlt => hnB ⟨i, hSt, hfm, hlt⟩
    have hie : i = f.vars.length := by omega
    obtain ⟨c', hsteps, hall, hpc', hG'⟩ :=
      scan_head_exit g env name out count pn r sp i f nameStr N φf φc m0 c hSt hfm hie hcnt
    exact ⟨c', hsteps, Or.inr ⟨hall, hpc', hG'⟩⟩
  · exact ⟨c, .refl c, Or.inl hHit⟩
  · exact ⟨c, .refl c, Or.inr hMiss⟩

end Vsa.Sim

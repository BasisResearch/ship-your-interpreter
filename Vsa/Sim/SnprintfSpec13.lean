import Vsa.Sim.SnprintfSpec12
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch01Part29

/-!
# M3 Layer-3 — `SnprintfSpec13` : reusable INDIRECT-TRANSFER dispatch helper (`_pd`)

The `svfprintf` `%`-conversion parse loop (and, structurally, `eval_expr`'s
`EX_*` dispatch and `value_equal`'s kind dispatch) picks its handler through a
`.rodata` **jump table**: an index `k` selects a signed 32-bit offset from the
table at `base + 4*k`, and the handler PC is `base + offset`.  The machine code is

```
  ... a5 := base + 4*k   (index address, from slli/srli/add) ...
  77b4: lw   a5,0(a5)      a5 := sext32( table[base + 4*k] )   (the offset)
  77b8: add  a5,a5,s6      a5 := offset + base                (the handler PC)
  77bc: jr   a5           PC := a5  (indirect jump, bit-0 cleared)
```

This module provides the **reusable** pieces every such dispatch needs:

* **`SlotPinnedAt base k target m`** — the jump-table slot pin, generalizing
  `EvalSimCommon.KindSlotPinned` over an arbitrary table base.  It pins the four
  little-endian bytes of slot `k` and states that their sign-extended reassembly
  plus `base` equals the handler PC `target`.  (`KindSlotPinned k armPC` is the
  `base = 0x80019f58` specialization.)
* **`ParseSlotPinned ch target m`** — the concrete instance for the `svfprintf`
  conversion-char table at `parseTableBase = 0x8001a0fc`, index `ch - 32`.  The
  decoded `%lld`-path targets (`parseSlot_l`, `parseSlot_d`) are exactly the
  ones the memory note records: `'l' (0x6c) → 0x80008534`, `'d' (0x64) → 0x80008008`.
* **`stepObs_jalr_indirect`** — the reusable indirect-transfer *site* helper: an
  indirect `jr rs1` / `jalr x0,0(rs1)` for an **arbitrary** `rs1` register value,
  landing PC := (`rs1` bit-0-cleared).  This is exactly the `ret`/`jr` step
  (`StepObs.stepObs_jr`) but named and documented for computed dispatch; the
  `value_equal` dispatch (`ValueEqualSites.site_80002888`, rs1 = x15) and this
  parse dispatch (rs1 = x15) are both instances.
* **`parseDispatchHop_spec`** — the verified `Steps` hop `0x800077b4 → target`:
  starting with `x15 = base + 4*k` (the slot address already computed) and
  `SlotPinnedAt base k target`, it runs the `lw`+`add`+`jr` and lands at the
  pinned handler PC.

Applied to the `%lld` path: with `parseSlot_l`, `parseDispatchHop_spec` proves the
first dispatch hop `0x800077b4 → 0x80008534` (the `'l'` length-modifier handler
entry); with `parseSlot_d`, `0x800077b4 → 0x80008008` (the `'d'` integer-conversion
handler).  The upstream `slli`/`srli`/`add` that compute the slot address
`base + 4*k` from the char are left to a follow-up (they need the
`(k<<32)>>30 = 4*k` bitvector fact); this module lands the load-and-transfer core
that couples the pinned table byte to the reached handler PC.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Registers consumed by the downstream sign/digit path and untouched by a
jump-table dispatch hop. -/
def DispatchPrintFrame (σ : MState) (v8 v23 v12 : BitVec 64) : Prop :=
  σ.regs.get? Register.x8 = some v8 ∧
  σ.regs.get? Register.x23 = some v23 ∧
  σ.regs.get? Register.x12 = some v12

theorem dispatchPrintFrame_alu {σ' σ : MState} {pc vm : BitVec 64}
    {rd : Register} {v : RegisterType rd} {v8 v23 v12 : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v))
    (h8 : (rd == Register.x8) = false) (h23 : (rd == Register.x23) = false)
    (h12 : (rd == Register.x12) = false) (h : DispatchPrintFrame σ v8 v23 v12) :
    DispatchPrintFrame σ' v8 v23 v12 := by
  rcases h with ⟨hx8, hx23, hx12⟩
  exact ⟨obs_alu_other hobs Register.x8 (by decide) (by decide) (by decide) (by decide)
      (by decide) h8 (by decide) (by decide) hx8,
    obs_alu_other hobs Register.x23 (by decide) (by decide) (by decide) (by decide)
      (by decide) h23 (by decide) (by decide) hx23,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide)
      (by decide) h12 (by decide) (by decide) hx12⟩

theorem dispatchPrintFrame_jr {σ' σ : MState} {pc vm tgt : BitVec 64}
    {v8 v23 v12 : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt))
    (h : DispatchPrintFrame σ v8 v23 v12) : DispatchPrintFrame σ' v8 v23 v12 := by
  rcases h with ⟨hx8, hx23, hx12⟩
  exact ⟨obs_jr_other hobs Register.x8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx8,
    obs_jr_other hobs Register.x23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx23,
    obs_jr_other hobs Register.x12 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx12⟩

/-! ## `SlotPinnedAt` — the reusable jump-table slot pin (arbitrary table base)

`SlotPinnedAt base k target m` says: in memory `m`, the four little-endian bytes
of jump-table slot `k` (at `base + 4*k`) are `t0..t3`, and their sign-extended
32-bit reassembly `sext(t3 ++ t2 ++ t1 ++ t0)` plus `ofNat base` equals the
handler PC `target`.  This is `EvalSimCommon.KindSlotPinned k target` with the
table base abstracted (that predicate hardwires `jumpTableBase = 0x80019f58`;
here `base` is a parameter, so the *same* helper serves `eval_expr`'s table
(`0x80019f58`), `value_equal`'s table (`0x80019ef8`) and `svfprintf`'s conversion
table (`0x8001a0fc`)). -/
def SlotPinnedAt (base k : Nat) (target : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∃ t0 t1 t2 t3 : BitVec 8,
    m[(base + 4 * k + 0 : Nat)]? = some t0 ∧
    m[(base + 4 * k + 1 : Nat)]? = some t1 ∧
    m[(base + 4 * k + 2 : Nat)]? = some t2 ∧
    m[(base + 4 * k + 3 : Nat)]? = some t3 ∧
    (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
      + BitVec.ofNat 64 base) = target

/-- Read the four pinned slot bytes at a **known** slot address `slotAddr = base +
4*k`.  Packages `SlotPinnedAt` for consumption by an `lw a5,0(a5)` site whose base
register already holds the slot address (so the load offset is `0`). -/
theorem slotPinnedAt_read {base k : Nat} {target : BitVec 64}
    {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : SlotPinnedAt base k target m) :
    ∃ t0 t1 t2 t3 : BitVec 8,
      m[(base + 4 * k + 0 : Nat)]? = some t0 ∧
      m[(base + 4 * k + 1 : Nat)]? = some t1 ∧
      m[(base + 4 * k + 2 : Nat)]? = some t2 ∧
      m[(base + 4 * k + 3 : Nat)]? = some t3 ∧
      (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
        + BitVec.ofNat 64 base) = target := h

/-! ## `ParseSlotPinned` — the `svfprintf` conversion-char table instance

The `%`-conversion dispatch table lives at `parseTableBase = 0x8001a0fc`
(`auipc s6,0x13; addi s6,s6,-1676`, `SnprintfSpec12.parseInit_spec`).  The
dispatch index for a conversion character `ch` is `ch - 32` (the `addiw a5,s8,-32`
at `0x800077a0`).  `ParseSlotPinned ch target m` is `SlotPinnedAt parseTableBase
(ch - 32) target m`. -/
@[reducible] def parseTableBase : Nat := 0x8001a0fc

def ParseSlotPinned (ch : Nat) (target : BitVec 64)
    (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  SlotPinnedAt parseTableBase (ch - 32) target m

/-- The `'l'` (length-modifier, `0x6c`) slot: index `76`, bytes `38 e4 fe ff`
(offset `0xfffee438 = -0x11bc8`), target `0x8001a0fc + (-0x11bc8) = 0x80008534`.
Decoded directly from the ELF `.rodata`. -/
theorem parseSlot_l {m : Std.ExtHashMap Nat (BitVec 8)}
    (h0 : m[(parseTableBase + 4 * (0x6c - 32) + 0 : Nat)]? = some (0x38 : BitVec 8))
    (h1 : m[(parseTableBase + 4 * (0x6c - 32) + 1 : Nat)]? = some (0xe4 : BitVec 8))
    (h2 : m[(parseTableBase + 4 * (0x6c - 32) + 2 : Nat)]? = some (0xfe : BitVec 8))
    (h3 : m[(parseTableBase + 4 * (0x6c - 32) + 3 : Nat)]? = some (0xff : BitVec 8)) :
    ParseSlotPinned 0x6c (0x80008534#64) m :=
  ⟨0x38#8, 0xe4#8, 0xfe#8, 0xff#8, h0, h1, h2, h3, by
    apply BitVec.eq_of_toNat_eq; decide⟩

/-- The `'d'` (integer conversion, `0x64`) slot: index `68`, bytes `0c df fe ff`
(offset `0xfffedf0c = -0x120f4`), target `0x8001a0fc + (-0x120f4) = 0x80008008`.
Decoded directly from the ELF `.rodata`. -/
theorem parseSlot_d {m : Std.ExtHashMap Nat (BitVec 8)}
    (h0 : m[(parseTableBase + 4 * (0x64 - 32) + 0 : Nat)]? = some (0x0c : BitVec 8))
    (h1 : m[(parseTableBase + 4 * (0x64 - 32) + 1 : Nat)]? = some (0xdf : BitVec 8))
    (h2 : m[(parseTableBase + 4 * (0x64 - 32) + 2 : Nat)]? = some (0xfe : BitVec 8))
    (h3 : m[(parseTableBase + 4 * (0x64 - 32) + 3 : Nat)]? = some (0xff : BitVec 8)) :
    ParseSlotPinned 0x64 (0x80008008#64) m :=
  ⟨0x0c#8, 0xdf#8, 0xfe#8, 0xff#8, h0, h1, h2, h3, by
    apply BitVec.eq_of_toNat_eq; decide⟩

/-! ## `stepObs_jalr_indirect` — the reusable indirect-transfer site helper

An indirect jump `jr rs1` (`jalr x0, 0(rs1)`) for an **arbitrary** source
register `rs1` whose value is the computed handler address.  The step sets
`PC := (rs1) &~ 1` (bit 0 cleared) and writes no link (rd = x0).  This is exactly
`StepObs.stepObs_jr` — the observation is `ReadsLikePost σ' (sigmaPost_jump_x0 …
tgt)` with `tgt = bit-0-cleared rs1` — restated with a dispatch-oriented name so
the computed-jump call sites (parse dispatch here, `value_equal`'s jump table in
`ValueEqualSites.site_80002888`, `eval_expr`'s `EX_*` dispatch) share one helper.
The `jr a5` at `0x800077bc` is the `rs1 = x15` instance. -/
theorem stepObs_jalr_indirect
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 : regidx) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) :=
  stepObs_jr σ i u pc vminstret vrs1 w imm rs1 b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt hi

/-! ## `parseDispatchHop_spec` — the verified dispatch hop `0x800077b4 → target`

Starting at the slot-load instruction `0x800077b4` with the index address already
computed in `x15` (`= base + 4*k`) and the table base in `x22` (`= base`), run

```
  77b4: lw  a5,0(a5)     a5 := sext32( slot bytes ) = offset
  77b8: add a5,a5,s6     a5 := offset + base = target
  77bc: jr  a5           PC := target
```

The `SlotPinnedAt base k target` hypothesis supplies the slot bytes and the
`offset + base = target` arithmetic; the geometric hypotheses place the slot in
readable RAM (the `.rodata` table) and pin the target 4-aligned so the indirect
jump's bit-0 clear is a no-op.  Lands `PC = target` at the handler entry. -/
theorem parseDispatchHop_spec
    (base k : Nat) (target vsp v6 v20 v25 v27 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hslot : SlotPinnedAt base k target c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800077b4#64))
    -- x15 (a5) already holds the slot address base + 4*k
    (hx15 : c.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 (base + 4 * k)))
    -- x22 (s6) holds the table base
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 base))
    -- x2 (sp) is threaded through for the caller's convenience
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    -- x6/x20/x25/x27 (t1 ll-flag / a4 width / s9 cursor / s11) threaded through:
    -- the hop (lw a5 / add a5 / jr a5) writes only x15 and PC, so these survive
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx25 : c.σ.regs.get? Register.x25 = some v25)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    -- the slot address = base + 4*k as a machine word
    (hslotaddr : (BitVec.ofNat 64 (base + 4 * k)
      + sign_extend (m := 64) (0x000#12)).toNat = base + 4 * k)
    -- the slot is readable `.rodata` RAM above HTIF, 4-aligned
    (hlo : 0x80000000 ≤ base + 4 * k)
    (hhiram : base + 4 * k + 4 ≤ 0x100000000)
    (hhtif : base + 4 * k + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base + 4 * k)
    (hslotalign : (base + 4 * k) % 4 = 0)
    -- the handler PC is 4-aligned (so the indirect jump's bit-0 clear is a no-op)
    (htgtalign : (BitVec.update (target + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC
        = some (BitVec.update (target + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some v6 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25 = some v25 ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      c'.σ.mem = c.σ.mem ∧
      (∀ v8 v23 v12, DispatchPrintFrame c.σ v8 v23 v12 →
        DispatchPrintFrame c'.σ v8 v23 v12) ∧
      c'.tick < 2 := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  -- the pinned slot bytes at the known slot address
  obtain ⟨t0, t1, t2, t3, hs0, hs1, hs2, hs3, htgteq⟩ := slotPinnedAt_read hslot
  -- rewrite the byte facts to the `x15 + off` effective address
  have hea : (BitVec.ofNat 64 (base + 4 * k) + sign_extend (m := 64) (0x000#12)).toNat
      = base + 4 * k := hslotaddr
  have hb0' : c.σ.mem[(BitVec.ofNat 64 (base + 4 * k) + sign_extend (m := 64) (0x000#12)).toNat]?
      = some t0 := by rw [hea]; exact hs0
  have hb1' : c.σ.mem[(BitVec.ofNat 64 (base + 4 * k) + sign_extend (m := 64) (0x000#12)).toNat + 1]?
      = some t1 := by rw [hea]; exact hs1
  have hb2' : c.σ.mem[(BitVec.ofNat 64 (base + 4 * k) + sign_extend (m := 64) (0x000#12)).toNat + 2]?
      = some t2 := by rw [hea]; exact hs2
  have hb3' : c.σ.mem[(BitVec.ofNat 64 (base + 4 * k) + sign_extend (m := 64) (0x000#12)).toNat + 3]?
      = some t3 := by rw [hea]; exact hs3
  -- the loaded offset value
  let voff : BitVec 64 :=
    sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
  -- === 77b4: lw a5,0(a5)  ⇒  x15 := voff ===
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077b4 hload
  have hx15n1 : (afterNextPC (afterPrelude c.σ) (0x800077b4#64)).regs.get? Register.x15
      = some (BitVec.ofNat 64 (base + 4 * k)) := by
    rw [get?_afterNextPC c.σ (0x800077b4#64) _ (by decide) (by decide)]; exact hx15
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x800077b4#64) vmi0 (0x0007a783#32)
      (instruction.LOAD (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, false, 4))
      Register.x15 voff (0x83#8) (0xa7#8) (0x07#8) (0x00#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0007a783 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (exec_lw c.σ (0x800077b4#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
        (sigma3_alu c.σ (0x800077b4#64) Register.x15 voff)
        (BitVec.ofNat 64 (base + 4 * k)) t0 t1 t2 t3 hG
        (rX_bits_x15 _ (BitVec.ofNat 64 (base + 4 * k)) hx15n1)
        (wX_bits_x15 _ voff)
        (by rw [hea]; exact hlo) (by rw [hea]; exact hhiram) (by rw [hea]; exact hhtif)
        (by rw [hea]; exact hslotalign) hb0' hb1' hb2' hb3')
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x800077b8#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800077b4#64 : BitVec 64) 4 = (0x800077b8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_1 : σ1.regs.get? Register.x15 = some voff :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx22_1 : σ1.regs.get? Register.x22 = some (BitVec.ofNat 64 base) :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx6_1 : σ1.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
  have hx25_1 : σ1.regs.get? Register.x25 = some v25 :=
    obs_alu_other hobs1 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25
  have hx27_1 : σ1.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs1 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have hframe1 : ∀ v8 v23 v12, DispatchPrintFrame c.σ v8 v23 v12 →
      DispatchPrintFrame σ1 v8 v23 v12 := fun _ _ _ h =>
    dispatchPrintFrame_alu hobs1 (by decide) (by decide) (by decide) h
  -- === 77b8: add a5,a5,s6  ⇒  x15 := voff + base = target ===
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077b8 hload1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x800077b8#64) vmi1 (0x016787b3#32)
      (instruction.RTYPE (regidx.Regidx 0x16#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
      Register.x15 (voff + BitVec.ofNat 64 base) (0xb3#8) (0x87#8) (0x67#8) (0x01#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_016787b3 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_rtype_add_char (regidx.Regidx 0x16#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
        voff (BitVec.ofNat 64 base) (afterNextPC (afterPrelude σ1) (0x800077b8#64))
        (sigma3_alu σ1 (0x800077b8#64) Register.x15 (voff + BitVec.ofNat 64 base))
        (rX_bits_x15 _ voff (by rw [get?_afterNextPC σ1 (0x800077b8#64) _ (by decide) (by decide)]; exact hx15_1))
        (rX_bits_x22 _ (BitVec.ofNat 64 base) (by rw [get?_afterNextPC σ1 (0x800077b8#64) _ (by decide) (by decide)]; exact hx22_1))
        (wX_bits_x15 _ (voff + BitVec.ofNat 64 base)))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x800077bc#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800077b8#64 : BitVec 64) 4 = (0x800077bc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  -- x15 now = voff + base; rewrite to = target
  have hx15_2raw : σ2.regs.get? Register.x15 = some (voff + BitVec.ofNat 64 base) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hvoffbase : voff + BitVec.ofNat 64 base = target := htgteq
  have hx15_2 : σ2.regs.get? Register.x15 = some target := by rw [hx15_2raw, hvoffbase]
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx6_2 : σ2.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs2 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx25_2 : σ2.regs.get? Register.x25 = some v25 :=
    obs_alu_other hobs2 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_1
  have hx27_2 : σ2.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs2 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hframe2 : ∀ v8 v23 v12, DispatchPrintFrame c.σ v8 v23 v12 →
      DispatchPrintFrame σ2 v8 v23 v12 := fun v8 v23 v12 h =>
    dispatchPrintFrame_alu hobs2 (by decide) (by decide) (by decide) (hframe1 v8 v23 v12 h)
  -- === 77bc: jr a5  ⇒  PC := target (bit 0 cleared) ===  (reusable indirect helper)
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077bc hload2
  have hx15n3 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ2) (0x800077bc#64))
      = .ok target (afterNextPC (afterPrelude σ2) (0x800077bc#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ2 (0x800077bc#64) _ (by decide) (by decide)]; exact hx15_2
  have hpc2mem : σ2.mem[(0x800077bc#64 : BitVec 64).toNat]? = some (0x67 : BitVec 8) := he0
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_jalr_indirect σ2 i2 (c.steps + 1 + 1) (0x800077bc#64) vmi2 target
      (0x00078067#32) (0x000#12) (regidx.Regidx 0x0f#5) (0x67#8) (0x80#8) (0x07#8) (0x00#8)
      hG2 hpc2 hmi2 he0 he1 he2 he3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00078067 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      hx15n3 htgtalign hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC
      = some (BitVec.update (target + sign_extend (m := 64) (0x000#12)) 0 0#1) :=
    obs_jr_pc hobs3
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_jr_other hobs3 Register.x2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx6_3 : σ3.regs.get? Register.x6 = some v6 :=
    obs_jr_other hobs3 Register.x6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_jr_other hobs3 Register.x20 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx25_3 : σ3.regs.get? Register.x25 = some v25 :=
    obs_jr_other hobs3 Register.x25 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx25_2
  have hx27_3 : σ3.regs.get? Register.x27 = some v27 :=
    obs_jr_other hobs3 Register.x27 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx27_2
  have hmemc : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  have hframe3 : ∀ v8 v23 v12, DispatchPrintFrame c.σ v8 v23 v12 →
      DispatchPrintFrame σ3 v8 v23 v12 := fun v8 v23 v12 h =>
    dispatchPrintFrame_jr hobs3 (hframe2 v8 v23 v12 h)
  -- assemble
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩, ?_, hG3, hpc3, hx2_3, hx6_3, hx20_3, hx25_3, hx27_3,
    hmemc, hframe3, hi3⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans (Steps.single hstep3))

/-! ## `%lld`-path application

The first `%lld` dispatch hop reaches the `'l'` length-modifier handler at
`0x80008534`; the `'d'` integer-conversion handler is at `0x80008008`.  Both fall
out of `parseDispatchHop_spec` with the corresponding `ParseSlotPinned` witness. -/

/-- `%lld` first dispatch: from the slot-load `0x800077b4` (slot address = `'l'`
slot, `parseTableBase + 4*(0x6c-32)`) to the `'l'` handler entry `0x80008534`. -/
theorem parseDispatch_l_spec
    (vsp v6 v20 v25 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hslot : ParseSlotPinned 0x6c (0x80008534#64) c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800077b4#64))
    (hx15 : c.σ.regs.get? Register.x15
      = some (BitVec.ofNat 64 (parseTableBase + 4 * (0x6c - 32))))
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx25 : c.σ.regs.get? Register.x25 = some v25)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80008534#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some v6 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25 = some v25 ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      c'.tick < 2 := by
  have h := parseDispatchHop_spec parseTableBase (0x6c - 32) (0x80008534#64) vsp v6 v20 v25 v27 c
    hG hload hslot hpc hx15 hx22 hx2 hx6 hx20 hx25 hx27
    (by decide) (by decide) (by decide)
    (by simp only [tohostAddr]; decide) (by decide) (by decide)
    htick
  obtain ⟨c', hsteps, hG', hpc', hx2', hx6', hx20', hx25', hx27', _hmem',
      _hframe', htick'⟩ := h
  refine ⟨c', hsteps, hG', ?_, hx2', hx6', hx20', hx25', hx27', htick'⟩
  rw [hpc']
  first
  | rfl
  | (congr 1; apply BitVec.eq_of_toNat_eq; decide)

/-- `%lld` `'d'` dispatch: from the slot-load `0x800077b4` (slot address = `'d'`
slot, `parseTableBase + 4*(0x64-32)`) to the `'d'` handler entry `0x80008008`. -/
theorem parseDispatch_d_spec
    (vsp v6 v20 v25 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hslot : ParseSlotPinned 0x64 (0x80008008#64) c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800077b4#64))
    (hx15 : c.σ.regs.get? Register.x15
      = some (BitVec.ofNat 64 (parseTableBase + 4 * (0x64 - 32))))
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx25 : c.σ.regs.get? Register.x25 = some v25)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80008008#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some v6 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25 = some v25 ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      c'.σ.mem = c.σ.mem ∧
      (∀ v8 v23 v12, DispatchPrintFrame c.σ v8 v23 v12 →
        DispatchPrintFrame c'.σ v8 v23 v12) ∧
      c'.tick < 2 := by
  have h := parseDispatchHop_spec parseTableBase (0x64 - 32) (0x80008008#64) vsp v6 v20 v25 v27 c
    hG hload hslot hpc hx15 hx22 hx2 hx6 hx20 hx25 hx27
    (by decide) (by decide) (by decide)
    (by simp only [tohostAddr]; decide) (by decide) (by decide)
    htick
  obtain ⟨c', hsteps, hG', hpc', hx2', hx6', hx20', hx25', hx27', hmem',
      hframe', htick'⟩ := h
  refine ⟨c', hsteps, hG', ?_, hx2', hx6', hx20', hx25', hx27', hmem', hframe', htick'⟩
  rw [hpc']
  first
  | rfl
  | (congr 1; apply BitVec.eq_of_toNat_eq; decide)

end Vsa.Sim

import Vsa.Sim.SnprintfSpec20
import Vsa.Sim.SnprintfSpec24
import Vsa.Sim.Mfr

/-!
# M3 Layer-3 — `SnprintfSpec25` : the composed svfprintf **flush return path**
## `0x8000e908` (the `jal __ssprint_r` completed) → svfprintf's `ret`, `a0 = total`

The glue for flush part 3b (pctrace `0x80008688 → 0x80007918 → parse-loop NUL
exit → epilogue 0x800079b0 → ret with a0 = mem[sp+16]`):

    ssprint_iov2_spec (SnprintfSpec20, r := 0x80008688)
      ≫ retA_spec (Spec21: beqz a0 / count clear / j loop head)
      ≫ retB_spec (Spec22: loop head + __locale_mb_cur_max + __ascii_mbtowc,
                   the NUL is read, mbtowc = 0)
      ≫ retC_spec (Spec23: pending-literal length = 0 → epilogue)
      ≫ retD_spec (Spec24: epilogue reloads → ret, a0 := mem[sp+16])

`ssprint_iov2_post` is consumed as the state at the return point: `a0 = 0` /
`PC = 0x80008688` discharge segment A's guards; its `Pin8 (q+16) 0` becomes the
`ld a5,240(sp) = 0` read; its pointwise six-window memory frame transports the
caller's prologue spills (`SlotHolds` at `sp+0x1e8 … sp+0x248`), the parse
state (`sp+0`, `sp+8`, `sp+16`, `sp+32`), the locale data pins and the format
NUL byte across the whole `__ssprint_r` call (`slotHolds_of_agree_rt`).

Residual caller obligations (all facts about the state at the `jal`, provided
by the earlier flush segments / the prologue when the full path is glued):
`PreSr` itself, the prologue spill slots, `mem[sp+32] = 0`, the fmt-NUL byte,
the FILE `_flags` bytes with bit 6 clear, `gp`/`s1`/locale-data constants, and
the address-layout disjointness hypotheses. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded __locale_mb_cur_maxLoaded
  __ascii_mbtowcLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Pointwise-agreement transports -/

/-- `SvfprintfSliceLoaded` (all pins in `[0x80007654, 0x80008b11)`) from a
pointwise agreement below `0x8000b000`. -/
theorem svfSlice_of_agree_rt {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, 0x80007654 ≤ a → a < 0x8000b000 → mem[a]? = m0[a]?)
    (h : SvfprintfSliceLoaded m0) :
    SvfprintfSliceLoaded mem := by
  unfold Vsa.Sim.Code.SvfprintfSliceLoaded at h ⊢
  simp only [Vsa.Sim.Code.svfprintfSliceChunk0, Vsa.Sim.Code.svfprintfSliceChunk1,
    Vsa.Sim.Code.svfprintfSliceChunk2, Vsa.Sim.Code.svfprintfSliceChunk3,
    Vsa.Sim.Code.svfprintfSliceChunk4, Vsa.Sim.Code.svfprintfSliceChunk5,
    Vsa.Sim.Code.svfprintfSliceChunk6, Vsa.Sim.Code.svfprintfSliceChunk7,
    Vsa.Sim.Code.svfprintfSliceChunk8, Vsa.Sim.Code.svfprintfSliceChunk9,
    Vsa.Sim.Code.svfprintfSliceChunk10, Vsa.Sim.Code.svfprintfSliceChunk11,
    Vsa.Sim.Code.svfprintfSliceChunk12, Vsa.Sim.Code.svfprintfSliceChunk13,
    Vsa.Sim.Code.svfprintfSliceChunk14, Vsa.Sim.Code.svfprintfSliceChunk15,
    Vsa.Sim.Code.svfprintfSliceChunk16, Vsa.Sim.Code.svfprintfSliceChunk17,
    Vsa.Sim.Code.svfprintfSliceChunk18, Vsa.Sim.Code.svfprintfSliceChunk19,
    Vsa.Sim.Code.svfprintfSliceChunk20, Vsa.Sim.Code.svfprintfSliceChunk21,
    Vsa.Sim.Code.svfprintfSliceChunk22, Vsa.Sim.Code.svfprintfSliceChunk23,
    Vsa.Sim.Code.svfprintfSliceChunk24, Vsa.Sim.Code.svfprintfSliceChunk25,
    Vsa.Sim.Code.svfprintfSliceChunk26, Vsa.Sim.Code.svfprintfSliceChunk27,
    Vsa.Sim.Code.svfprintfSliceChunk28, Vsa.Sim.Code.svfprintfSliceChunk29,
    Vsa.Sim.Code.svfprintfSliceChunk30, Vsa.Sim.Code.svfprintfSliceChunk31,
    Vsa.Sim.Code.svfprintfSliceChunk32, Vsa.Sim.Code.svfprintfSliceChunk33] at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- `FlushPinsLoaded` (all pins in `[0x80007a00, 0x8000a83c)`) from a pointwise
agreement on `[0x80007654, 0x8000b000)` (two-sided variant of
`Code.flushPins_of_agree`, needed because the agreement only holds on the
actual code ranges here). -/
theorem flushPins_of_agree_rt {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, 0x80007654 ≤ a → a < 0x8000b000 → mem[a]? = m0[a]?)
    (h : FlushPinsLoaded m0) : FlushPinsLoaded mem := by
  unfold Vsa.Sim.Code.FlushPinsLoaded Vsa.Sim.Code.flushPinsChunk0 at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- `__locale_mb_cur_maxLoaded` (pins in `[0x80010234, 0x8001023c)`) from a
pointwise agreement on `[0x80010234, 0x800122d0)`. -/
theorem locale_of_agree_rt {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, 0x80010234 ≤ a → a < 0x800122d0 → mem[a]? = m0[a]?)
    (h : __locale_mb_cur_maxLoaded m0) : __locale_mb_cur_maxLoaded mem := by
  unfold Vsa.Sim.Code.__locale_mb_cur_maxLoaded at h ⊢
  simp only [Vsa.Sim.Code.__locale_mb_cur_maxChunk0] at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- `__ascii_mbtowcLoaded` (pins in `[0x80012268, 0x800122d0)`) from the same
agreement window. -/
theorem amb_of_agree_rt {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, 0x80010234 ≤ a → a < 0x800122d0 → mem[a]? = m0[a]?)
    (h : __ascii_mbtowcLoaded m0) : __ascii_mbtowcLoaded mem := by
  unfold Vsa.Sim.Code.__ascii_mbtowcLoaded at h ⊢
  simp only [Vsa.Sim.Code.__ascii_mbtowcChunk0, Vsa.Sim.Code.__ascii_mbtowcChunk1] at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- `__locale_mb_cur_maxLoaded` survives a byte store at/above `0x80014000`. -/
theorem locale_insert_rt (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80014000 ≤ k) (h : __locale_mb_cur_maxLoaded mem) :
    __locale_mb_cur_maxLoaded (mem.insert k v) := by
  unfold Vsa.Sim.Code.__locale_mb_cur_maxLoaded at h ⊢
  simp only [Vsa.Sim.Code.__locale_mb_cur_maxChunk0] at h ⊢
  simp (disch := omega) only [getElem?_insert_above_rt mem k v hk]
  exact h

theorem locale_writeMap4_rt (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4))
    (ha : 0x80014000 ≤ a) (h : __locale_mb_cur_maxLoaded mem) :
    __locale_mb_cur_maxLoaded (writeMap4 mem a d) :=
  locale_insert_rt _ _ _ (by omega) (locale_insert_rt _ _ _ (by omega)
    (locale_insert_rt _ _ _ (by omega) (locale_insert_rt _ _ _ (by omega) h)))

/-- Rebuild a `SlotHolds` on the other side of a pointwise-agreeing memory
transition, with the slot's effective address given explicitly (`hA`). -/
theorem slotHolds_of_agree_rt (base : BitVec 64) (off : Nat) (v : BitVec 64) (A : Nat)
    (mem' mem : Std.ExtHashMap Nat (BitVec 8))
    (hA : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A)
    (hag : ∀ a, A ≤ a → a < A + 8 → mem'[a]? = mem[a]?)
    (h : SlotHolds base off v mem) : SlotHolds base off v mem' := by
  unfold SlotHolds at h ⊢
  rw [hA] at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(hag _ (by omega) (by omega)).trans h0, (hag _ (by omega) (by omega)).trans h1,
    (hag _ (by omega) (by omega)).trans h2, (hag _ (by omega) (by omega)).trans h3,
    (hag _ (by omega) (by omega)).trans h4, (hag _ (by omega) (by omega)).trans h5,
    (hag _ (by omega) (by omega)).trans h6, (hag _ (by omega) (by omega)).trans h7⟩

/-- A `Pin8` at the slot's effective address *is* the `SlotHolds`. -/
theorem slotHolds_of_pin8_rt (base : BitVec 64) (off : Nat) (v : BitVec 64) (A : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (hA : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A)
    (h : Pin8 mem A v) : SlotHolds base off v mem := by
  unfold SlotHolds
  rw [hA]
  exact h

/-! ## The composed theorem -/

/-- **The svfprintf flush return path, end to end.**

From the completed `jal __ssprint_r` (the state `iov2ToSsprintCall_spec`
reaches: `PC = 0x8000e908`, `ra = 0x80008688`, `PreSr` holding with
`r := 0x80008688`) through the 2-iovec flush (`ssprint_iov2_spec`), the
post-call cleanup, the parse-loop NUL exit (both locale helper calls inlined),
and svfprintf's epilogue, to `PC = vra0` with **`a0 = vtot` — the total that
svfprintf returns** (`mem[sp+16]`, written before the call by
`iov2ToSsprintCall_spec`). -/
theorem svfprintf_flushReturn_spec
    (g : (R : Register) → Option (RegisterType R))
    (q viov p d s1 s2 vsp v8 v18 v19 v20 v21 va0 : BitVec 64)
    (vcur vra0 vtot vS0o vS1o vS2 vS3 vS4 vS5 vS6o vS7 vS8 vS9 vS10 vS11 : BitVec 64)
    (fl0 fl1 : BitVec 8)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) (c : Config)
    (hPre : PreSr g (0x80008688#64) q viov p d s1 s2 vsp v8 (0x8001b798#64) v18 v19 v20 v21
      va0 n1 n2 cap32 m0 bs1 bs2 c)
    -- code / static-data pins at the call
    (hsliceL : SvfprintfSliceLoaded m0)
    (hfpL : FlushPinsLoaded m0)
    (hlocL : __locale_mb_cur_maxLoaded m0)
    (hambL : __ascii_mbtowcLoaded m0)
    (hgx3 : g Register.x3 = some (0x8001b510#64))
    (hfnslot : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) m0)
    (hmb : m0[(0x8001b8f8 : Nat)]? = some (0x01#8))
    -- caller stack slots at the call (prologue spills + parse state + total)
    (hs000 : SlotHolds vsp 0x000 vcur m0)
    (hs008 : SlotHolds vsp 0x008 p m0)
    (hs010 : SlotHolds vsp 0x010 vtot m0)
    (hs020 : SlotHolds vsp 0x020 (0#64) m0)
    (hs1e8 : SlotHolds vsp 0x1e8 vS11 m0)
    (hs1f0 : SlotHolds vsp 0x1f0 vS10 m0)
    (hs1f8 : SlotHolds vsp 0x1f8 vS9 m0)
    (hs200 : SlotHolds vsp 0x200 vS8 m0)
    (hs208 : SlotHolds vsp 0x208 vS7 m0)
    (hs210 : SlotHolds vsp 0x210 vS6o m0)
    (hs218 : SlotHolds vsp 0x218 vS5 m0)
    (hs220 : SlotHolds vsp 0x220 vS4 m0)
    (hs228 : SlotHolds vsp 0x228 vS3 m0)
    (hs230 : SlotHolds vsp 0x230 vS2 m0)
    (hs238 : SlotHolds vsp 0x238 vS1o m0)
    (hs240 : SlotHolds vsp 0x240 vS0o m0)
    (hs248 : SlotHolds vsp 0x248 vra0 m0)
    -- the format NUL and the FILE flags
    (hnul : m0[vcur.toNat]? = some (0x00#8))
    (hfl0 : m0[p.toNat + 16]? = some fl0)
    (hfl1 : m0[p.toNat + 17]? = some fl1)
    (hflag : ((zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
      &&& sign_extend (m := 64) (0x040#12)) = 0#64)
    -- layout
    (hqv : q.toNat = vsp.toNat + 224)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (hdlay : 0x8001b900 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ 0x80007654)
    (hplay : 0x8001b900 ≤ p.toNat ∨ p.toNat + 18 ≤ 0x80007654)
    (hdstk : vsp.toNat + 592 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ vsp.toNat - 128)
    (hpstk : vsp.toNat + 592 ≤ p.toNat ∨ p.toNat + 18 ≤ vsp.toNat - 128)
    (hpd18 : p.toNat + 18 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ p.toNat)
    (hcurd : vcur.toNat + 1 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ vcur.toNat)
    (hcurp : vcur.toNat + 1 ≤ p.toNat ∨ p.toNat + 16 ≤ vcur.toNat)
    (hcurstk : vcur.toNat + 1 ≤ vsp.toNat - 128 ∨ vsp.toNat + 592 ≤ vcur.toNat)
    (hcurlo : 0x80000000 ≤ vcur.toNat)
    (hcurhi : vcur.toNat + 1 ≤ 0x100000000)
    (hcurhtif : vcur.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vcur.toNat)
    (hp18hi : p.toNat + 18 ≤ 0x100000000)
    (hra0align : vra0.toNat % 4 = 0) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some vra0 ∧
      c'.σ.regs.get? Register.x1 = some vra0 ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (592#64)) ∧
      c'.σ.regs.get? Register.x10 = some vtot ∧
      c'.σ.regs.get? Register.x8 = some vS0o ∧
      c'.σ.regs.get? Register.x9 = some vS1o ∧
      c'.σ.regs.get? Register.x18 = some vS2 ∧
      c'.σ.regs.get? Register.x19 = some vS3 ∧
      c'.σ.regs.get? Register.x20 = some vS4 ∧
      c'.σ.regs.get? Register.x21 = some vS5 ∧
      c'.σ.regs.get? Register.x22 = some vS6o ∧
      c'.σ.regs.get? Register.x23 = some vS7 ∧
      c'.σ.regs.get? Register.x24 = some vS8 ∧
      c'.σ.regs.get? Register.x25 = some vS9 ∧
      c'.σ.regs.get? Register.x26 = some vS10 ∧
      c'.σ.regs.get? Register.x27 = some vS11 ∧
      (∀ k, k < n1 → c'.σ.mem[(d.toNat + k)]? = some (bs1 k)) ∧
      (∀ k, k < n2 → c'.σ.mem[(d.toNat + n1 + k)]? = some (bs2 k)) ∧
      Pin8 c'.σ.mem p.toNat (d + BitVec.ofNat 64 (n1 + n2)) ∧
      Pin4 c'.σ.mem (p.toNat + 12) (cap32 - BitVec.ofNat 32 n1 - BitVec.ofNat 32 n2) ∧
      Pin8 c'.σ.mem (q.toNat + 16) (0#64 : BitVec 64) ∧
      Pin4 c'.σ.mem (q.toNat + 8) (0#32 : BitVec 32) ∧
      Pin4 c'.σ.mem (vsp.toNat + 180) (0#32 : BitVec 32) ∧
      (∀ a, ¬(d.toNat ≤ a ∧ a < d.toNat + n1 + n2) →
        ¬(p.toNat ≤ a ∧ a < p.toNat + 8) → ¬(p.toNat + 12 ≤ a ∧ a < p.toNat + 16) →
        ¬(q.toNat + 8 ≤ a ∧ a < q.toNat + 12) → ¬(q.toNat + 16 ≤ a ∧ a < q.toNat + 24) →
        ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat) →
        ¬(vsp.toNat + 180 ≤ a ∧ a < vsp.toNat + 184) →
        c'.σ.mem[a]? = m0[a]?) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hreg := hPre.regions
  have hplo := hreg.p_lo
  have hpal := hreg.p_align
  have hdlo := hreg.d_lo
  have hdhiR := hreg.d_hi
  have hn131 := hreg.n1_31; have hn231 := hreg.n2_31
  have hnw : vsp.toNat + 592 < 2 ^ 64 := by omega
  -- ============ the __ssprint_r flush itself ============
  obtain ⟨c1, hstepsSr, hpostSr⟩ :=
    ssprint_iov2_spec g (0x80008688#64) q viov p d s1 s2 vsp v8 (0x8001b798#64) v18 v19 v20
      v21 va0 n1 n2 cap32 m0 bs1 bs2 (by decide) c hPre
  obtain ⟨hG1, hpc1, ha0_1, hra1, hsp1, hx8_1, hx9_1, hx18_1, hx19_1, hx20_1, hx21_1,
    hcp1, hcp2, hcurspin, hcappin, hresidpin, hcountpin, hmframe, htick1, hgframe1⟩ := hpostSr
  -- pointwise agreements out of the six-window frame
  have hagStatic : ∀ a : Nat, (0x80007654 ≤ a ∧ a < 0x8000b000)
      ∨ (0x80010234 ≤ a ∧ a < 0x800122d0)
      ∨ (0x8001b880 ≤ a ∧ a < 0x8001b900) → c1.σ.mem[a]? = m0[a]? := by
    intro a ha
    exact hmframe a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hagStack : ∀ a : Nat, vsp.toNat ≤ a → a < vsp.toNat + 592 →
      (a < vsp.toNat + 232 ∨ vsp.toNat + 248 ≤ a) → c1.σ.mem[a]? = m0[a]? := by
    intro a h1 h2 h3
    exact hmframe a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hagCur : c1.σ.mem[vcur.toNat]? = m0[vcur.toNat]? :=
    hmframe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hagFl0 : c1.σ.mem[p.toNat + 16]? = m0[p.toNat + 16]? :=
    hmframe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hagFl1 : c1.σ.mem[p.toNat + 17]? = m0[p.toNat + 17]? :=
    hmframe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- code/data pins at the return point
  have hslice1 : SvfprintfSliceLoaded c1.σ.mem :=
    svfSlice_of_agree_rt (fun a h1 h2 => hagStatic a (Or.inl ⟨h1, h2⟩)) hsliceL
  have hfp1 : FlushPinsLoaded c1.σ.mem :=
    flushPins_of_agree_rt (fun a h1 h2 => hagStatic a (Or.inl ⟨h1, h2⟩)) hfpL
  have hloc1 : __locale_mb_cur_maxLoaded c1.σ.mem :=
    locale_of_agree_rt (fun a h1 h2 => hagStatic a (Or.inr (Or.inl ⟨h1, h2⟩))) hlocL
  have hamb1 : __ascii_mbtowcLoaded c1.σ.mem :=
    amb_of_agree_rt (fun a h1 h2 => hagStatic a (Or.inr (Or.inl ⟨h1, h2⟩))) hambL
  have hfn1 : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) c1.σ.mem :=
    slotHolds_of_agree_rt _ _ _ 0x8001b880 _ _ (by decide)
      (fun a h1 h2 => hagStatic a (Or.inr (Or.inr (by omega)))) hfnslot
  have hmb1 : c1.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8) :=
    (hagStatic _ (Or.inr (Or.inr (by omega)))).trans hmb
  have hnul1 : c1.σ.mem[vcur.toNat]? = some (0x00#8) := hagCur.trans hnul
  -- slot effective addresses
  have hA000 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x000)).toNat = vsp.toNat + 0 :=
    ptr_addoff vsp _ 0 (by decide) (by omega)
  have hA008 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x008)).toNat = vsp.toNat + 8 :=
    ptr_addoff vsp _ 8 (by decide) (by omega)
  have hA010 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x010)).toNat = vsp.toNat + 16 :=
    ptr_addoff vsp _ 16 (by decide) (by omega)
  have hA020 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x020)).toNat = vsp.toNat + 32 :=
    ptr_addoff vsp _ 32 (by decide) (by omega)
  have hA0f0 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x0f0)).toNat = vsp.toNat + 240 :=
    ptr_addoff vsp _ 240 (by decide) (by omega)
  have hA1e8 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x1e8)).toNat = vsp.toNat + 488 :=
    ptr_addoff vsp _ 488 (by decide) (by omega)
  have hA1f0 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x1f0)).toNat = vsp.toNat + 496 :=
    ptr_addoff vsp _ 496 (by decide) (by omega)
  have hA1f8 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x1f8)).toNat = vsp.toNat + 504 :=
    ptr_addoff vsp _ 504 (by decide) (by omega)
  have hA200 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x200)).toNat = vsp.toNat + 512 :=
    ptr_addoff vsp _ 512 (by decide) (by omega)
  have hA208 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x208)).toNat = vsp.toNat + 520 :=
    ptr_addoff vsp _ 520 (by decide) (by omega)
  have hA210 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x210)).toNat = vsp.toNat + 528 :=
    ptr_addoff vsp _ 528 (by decide) (by omega)
  have hA218 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x218)).toNat = vsp.toNat + 536 :=
    ptr_addoff vsp _ 536 (by decide) (by omega)
  have hA220 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x220)).toNat = vsp.toNat + 544 :=
    ptr_addoff vsp _ 544 (by decide) (by omega)
  have hA228 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x228)).toNat = vsp.toNat + 552 :=
    ptr_addoff vsp _ 552 (by decide) (by omega)
  have hA230 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x230)).toNat = vsp.toNat + 560 :=
    ptr_addoff vsp _ 560 (by decide) (by omega)
  have hA238 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x238)).toNat = vsp.toNat + 568 :=
    ptr_addoff vsp _ 568 (by decide) (by omega)
  have hA240 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x240)).toNat = vsp.toNat + 576 :=
    ptr_addoff vsp _ 576 (by decide) (by omega)
  have hA248 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x248)).toNat = vsp.toNat + 584 :=
    ptr_addoff vsp _ 584 (by decide) (by omega)
  -- ============ segment A: 0x80008688 → 0x80007720 ============
  have hx3c1 : c1.σ.regs.get? Register.x3 = some (0x8001b510#64) :=
    (hgframe1 Register.x3 (by decide)).trans hgx3
  have hs020c1 : SlotHolds vsp 0x020 (0#64) c1.σ.mem :=
    slotHolds_of_agree_rt vsp 0x020 (0#64) (vsp.toNat + 32) _ _ hA020
      (fun a h1 h2 => hagStack a (by omega) (by omega) (by omega)) hs020
  obtain ⟨c2, hstA, hG2, hpc2, hx2_2, hx3_2, hx8_2, hx9_2, hx21_2, hx23_2, hmem2, hslice2,
      hfp2, htick2, hmi2⟩ :=
    retA_spec vsp v21 (0x8001b510#64) v8 (0x8001b798#64) c1 hG1 hslice1 hfp1 hpc1 ha0_1
      hsp1 hx3c1 hx8_1 hx9_1 hx21_1 hs020c1 (by omega) hsphi hspal htick1
  -- ============ segment B: 0x80007720 → 0x80007960 ============
  have hloc2 : __locale_mb_cur_maxLoaded c2.σ.mem := by
    rw [hmem2]; exact locale_writeMap4_rt _ _ _ (by omega) hloc1
  have hamb2 : __ascii_mbtowcLoaded c2.σ.mem := by
    rw [hmem2]; exact amb_writeMap4_rt _ _ _ (by omega) hamb1
  have hs000c1 : SlotHolds vsp 0x000 vcur c1.σ.mem :=
    slotHolds_of_agree_rt vsp 0x000 vcur (vsp.toNat + 0) _ _ hA000
      (fun a h1 h2 => hagStack a (by omega) (by omega) (by omega)) hs000
  have hs000c2 : SlotHolds vsp 0x000 vcur c2.σ.mem := by
    rw [hmem2]
    exact slot_survives_writeMap4 _ _ _ _ _ _ (Or.inr (by rw [hA000]; omega)) hs000c1
  have hfn2 : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) c2.σ.mem := by
    rw [hmem2]
    exact slot_survives_writeMap4 _ _ _ _ _ _
      (Or.inr (by rw [show ((0x8001b798#64 : BitVec 64) + sign_extend (m := 64)
        (BitVec.ofNat 12 0x0e8)).toNat = 0x8001b880 from by decide]; omega)) hfn1
  have hmb2 : c2.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8) := by
    rw [hmem2]
    exact (getElem?_writeMap4_out _ _ _ _ (by omega)).trans hmb1
  have hnul2 : c2.σ.mem[vcur.toNat]? = some (0x00#8) := by
    rw [hmem2]
    exact (getElem?_writeMap4_out _ _ _ _ (by omega)).trans hnul1
  obtain ⟨c3, hstB, hG3, hpc3, hx2_3, hx8_3, hx22_3, hx10_3, hmem3, hslice3, hfp3, htick3,
      hmi3⟩ :=
    retB_spec vsp vcur v8 c2 hG2 hslice2 hfp2 hloc2 hamb2 hpc2 hx2_2 hx3_2 hx8_2 hx9_2
      hs000c2 hfn2 hmb2 hnul2 hcurlo hcurhi hcurhtif (by omega) (by omega) hsphi hspal htick2
  -- ============ segment C: 0x80007960 → 0x800079b0 ============
  have hs000c3 : SlotHolds vsp 0x000 vcur c3.σ.mem := by
    rw [hmem3]
    exact slot_survives_writeMap4 _ _ _ _ _ _ (Or.inr (by rw [hA000]; omega)) hs000c2
  obtain ⟨c4, hstC, hG4, hpc4, hx2_4, hmem4, htick4, hmi4⟩ :=
    retC_spec vsp vcur (0#64) c3 hG3 hslice3 hfp3 hpc3 hx2_3 hx10_3 hx22_3 hs000c3
      (by omega) hsphi hspal htick3
  -- ============ segment D: 0x800079b0 → ret ============
  have hslice4 : SvfprintfSliceLoaded c4.σ.mem := hmem4 ▸ hslice3
  have hfp4 : FlushPinsLoaded c4.σ.mem := hmem4 ▸ hfp3
  have hmem34 : c4.σ.mem
      = writeMap4 (writeMap4 c1.σ.mem (vsp.toNat + 232) (swData (0#64)))
        (vsp.toNat + 180) (swData (0#64)) := by
    rw [hmem4, hmem3, hmem2]
  have hslotC4 : ∀ (off : Nat) (v : BitVec 64) (A : Nat),
      (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A →
      vsp.toNat ≤ A → A + 8 ≤ vsp.toNat + 592 →
      (A + 8 ≤ vsp.toNat + 180 ∨ vsp.toNat + 184 ≤ A) →
      (A + 8 ≤ vsp.toNat + 232 ∨ vsp.toNat + 248 ≤ A) →
      SlotHolds vsp off v m0 → SlotHolds vsp off v c4.σ.mem := by
    intro off v A hA h1 h2 h3 h4 h
    have hc1 : SlotHolds vsp off v c1.σ.mem :=
      slotHolds_of_agree_rt vsp off v A _ _ hA
        (fun a ha1 ha2 => hagStack a (by omega) (by omega) (by omega)) h
    rw [hmem34]
    exact slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hA]; omega)
      (slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hA]; omega) hc1)
  have h008c4 := hslotC4 0x008 p _ hA008 (by omega) (by omega) (by omega) (by omega) hs008
  have h010c4 := hslotC4 0x010 vtot _ hA010 (by omega) (by omega) (by omega) (by omega) hs010
  have h1e8c4 := hslotC4 0x1e8 vS11 _ hA1e8 (by omega) (by omega) (by omega) (by omega) hs1e8
  have h1f0c4 := hslotC4 0x1f0 vS10 _ hA1f0 (by omega) (by omega) (by omega) (by omega) hs1f0
  have h1f8c4 := hslotC4 0x1f8 vS9 _ hA1f8 (by omega) (by omega) (by omega) (by omega) hs1f8
  have h200c4 := hslotC4 0x200 vS8 _ hA200 (by omega) (by omega) (by omega) (by omega) hs200
  have h208c4 := hslotC4 0x208 vS7 _ hA208 (by omega) (by omega) (by omega) (by omega) hs208
  have h210c4 := hslotC4 0x210 vS6o _ hA210 (by omega) (by omega) (by omega) (by omega) hs210
  have h218c4 := hslotC4 0x218 vS5 _ hA218 (by omega) (by omega) (by omega) (by omega) hs218
  have h220c4 := hslotC4 0x220 vS4 _ hA220 (by omega) (by omega) (by omega) (by omega) hs220
  have h228c4 := hslotC4 0x228 vS3 _ hA228 (by omega) (by omega) (by omega) (by omega) hs228
  have h230c4 := hslotC4 0x230 vS2 _ hA230 (by omega) (by omega) (by omega) (by omega) hs230
  have h238c4 := hslotC4 0x238 vS1o _ hA238 (by omega) (by omega) (by omega) (by omega) hs238
  have h240c4 := hslotC4 0x240 vS0o _ hA240 (by omega) (by omega) (by omega) (by omega) hs240
  have h248c4 := hslotC4 0x248 vra0 _ hA248 (by omega) (by omega) (by omega) (by omega) hs248
  -- the gather cursor slot: cleared by __ssprint_r (its post's `Pin8 (q+16) 0`)
  have h0f0c1 : SlotHolds vsp 0x0f0 (0#64) c1.σ.mem :=
    slotHolds_of_pin8_rt vsp 0x0f0 (0#64) (q.toNat + 16) _ (by rw [hA0f0]; omega) hresidpin
  have h0f0c4 : SlotHolds vsp 0x0f0 (0#64) c4.σ.mem := by
    rw [hmem34]
    exact slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hA0f0]; omega)
      (slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hA0f0]; omega) h0f0c1)
  -- FILE flags bytes
  have hfl0c4 : c4.σ.mem[p.toNat + 16]? = some fl0 := by
    rw [hmem34]
    exact (getElem?_writeMap4_out _ _ _ _ (by omega)).trans
      ((getElem?_writeMap4_out _ _ _ _ (by omega)).trans (hagFl0.trans hfl0))
  have hfl1c4 : c4.σ.mem[p.toNat + 17]? = some fl1 := by
    rw [hmem34]
    exact (getElem?_writeMap4_out _ _ _ _ (by omega)).trans
      ((getElem?_writeMap4_out _ _ _ _ (by omega)).trans (hagFl1.trans hfl1))
  obtain ⟨c5, hstD, hG5, hpc5, hx1_5, hx2_5, hx10_5, hx8_5, hx9_5, hx18_5, hx19_5, hx20_5,
      hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hmem5, htick5, hmi5⟩ :=
    retD_spec vsp p vra0 vtot vS0o vS1o vS2 vS3 vS4 vS5 vS6o vS7 vS8 vS9 vS10 vS11 fl0 fl1
      c4 hG4 hslice4 hfp4 hpc4 hx2_4 h0f0c4 h008c4 h230c4 h228c4 h220c4 h218c4 h208c4
      h200c4 h1f8c4 h1f0c4 h1e8c4 h248c4 h240c4 h010c4 h238c4 h210c4 hfl0c4 hfl1c4 hflag
      (by omega) hp18hi (by omega) (by omega) hra0align (by omega) hsphi hspal htick4
  -- ============ final assembly ============
  have hmemF : c5.σ.mem
      = writeMap4 (writeMap4 c1.σ.mem (vsp.toNat + 232) (swData (0#64)))
        (vsp.toNat + 180) (swData (0#64)) := by
    rw [hmem5]; exact hmem34
  refine ⟨c5, hstepsSr.trans (hstA.trans (hstB.trans (hstC.trans hstD))), hG5, hpc5, hx1_5,
    hx2_5, hx10_5, hx8_5, hx9_5, hx18_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
    hx25_5, hx26_5, hx27_5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htick5, hmi5⟩
  · -- the first iovec (sign byte) window
    intro k hk
    rw [hmemF, getElem?_writeMap4_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega)]
    exact hcp1 k hk
  · -- the second iovec (digits) window
    intro k hk
    rw [hmemF, getElem?_writeMap4_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega)]
    exact hcp2 k hk
  · -- sink cursor
    refine Pin8_frame (fun k h1 h2 => ?_) hcurspin
    rw [hmemF, getElem?_writeMap4_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega)]
  · -- sink capacity
    refine Pin4_frame (fun k h1 h2 => ?_) hcappin
    rw [hmemF, getElem?_writeMap4_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega)]
  · -- gather resid (q+16) still 0
    refine Pin8_frame (fun k h1 h2 => ?_) hresidpin
    rw [hmemF, getElem?_writeMap4_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega)]
  · -- gather count (q+8): re-zeroed by the `sw zero,232(sp)`
    have h6 : Pin4 c5.σ.mem (vsp.toNat + 232) (swData (0#64)) := by
      rw [hmemF]
      exact Pin4_frame (fun k h1 h2 => getElem?_writeMap4_out _ _ _ _ (by omega))
        (Pin4_writeMap4 _ _ _)
    rw [show q.toNat + 8 = vsp.toNat + 232 from by omega, ← swData_zero_sr']
    exact h6
  · -- the wide-char out-parameter (sp+180): zeroed by __ascii_mbtowc
    have h7 : Pin4 c5.σ.mem (vsp.toNat + 180) (swData (0#64)) := by
      rw [hmemF]; exact Pin4_writeMap4 _ _ _
    rw [← swData_zero_sr']
    exact h7
  · -- the pointwise frame
    intro a hW1 hW2 hW3 hW4 hW5 hW6 hW7
    rw [hmemF, getElem?_writeMap4_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega)]
    exact hmframe a hW1 hW2 hW3 hW4 hW5 hW6

end Vsa.Sim

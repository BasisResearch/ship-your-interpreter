import VsaIris.Vsa.StdioRead
import Vsa.Sim.ExitRuntimeDataTransport

/-!
# `StdioOK` after a stdout write (lane N1)

A flushed stdout write leaves newlib's data as it found it, except `stdout`'s
`_p`, `_w` and `_flags` (rewritten with their idle values) and its one-byte
buffer (the last character). `StdioOK.written`: an image that agrees with a
`StdioOK` image off those bytes and holds the idle values there is `StdioOK`.
-/

namespace VsaIris.Stdio

open Vsa.MemRepr Vsa.Sim VsaIris.Interp

/-- The bytes a stdout write changes in newlib's data. -/
def outW (a : Nat) : Prop :=
  (0x8001bb20 ≤ a ∧ a < 0x8001bb28) ∨ (0x8001bb2c ≤ a ∧ a < 0x8001bb32) ∨ a = 0x8001bb97

theorem readLE_of_img {m : Mem} {f : Nat → BitVec 8} :
    ∀ {n a : Nat}, (∀ i, i < n → m[a + i]? = some (f (a + i))) → readLE m a n = some (imgLE f a n)
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have ih := readLE_of_img (n := n) (a := a + 1) fun i hi => by
      have := h (i + 1) (by omega); rwa [show a + (i + 1) = a + 1 + i by omega] at this
    simp [readLE, h0, ih, imgLE]

/-- A region inside newlib's data and off the written bytes. -/
def RegionOK (r : Nat × Nat) : Prop :=
  (0x8001b520 ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001b538 ∨ 0x8001b53c ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001b960 ∨
    0x8001b970 ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001b990 ∨ 0x8001b9b0 ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001ba08 ∨
    0x8001ba0c ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001ba18 ∨ 0x8001ba68 ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001c168) ∧
  (r.1 + r.2 ≤ 0x8001bb20 ∨ 0x8001bb28 ≤ r.1) ∧ (r.1 + r.2 ≤ 0x8001bb2c ∨ 0x8001bb32 ≤ r.1) ∧
  (r.1 + r.2 ≤ 0x8001bb97 ∨ 0x8001bb98 ≤ r.1)

instance (r : Nat × Nat) : Decidable (RegionOK r) := by unfold RegionOK; infer_instance

theorem exitExtra_regions : ∀ r ∈ exitRuntimeExtraRegions, RegionOK r := by decide

theorem exitExtra_off {a : Nat} (h : ExitRuntimeExtraFoot a) : stdioFoot a ∧ ¬ outW a := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have := exitExtra_regions r hr
  unfold RegionOK at this
  unfold stdioFoot InRange outW
  omega

/-- **`StdioOK` after a flushed stdout write.** -/
theorem StdioOK.written {img img' : Nat → BitVec 8} (h : StdioOK img)
    (hkeep : ∀ a, stdioFoot a → ¬ outW a → img' a = img a)
    (hp : imgLE img' 0x8001bb20 8 = 0x8001bb97) (hw : imgLE img' 0x8001bb2c 4 = 0)
    (hf : imgLE img' 0x8001bb30 2 = 0x200a) : StdioOK img' := by
  intro m hm
  obtain ⟨hc, he, hs, hl, hst⟩ := h.facts
  have hag : AgreeP (fun a => stdioFoot a ∧ ¬ outW a) (fillMem img dataList) m := fun a ha => by
    rw [fillMem_get img (mem_dataList ha.1), hm a ha.1, hkeep a ha.1 ha.2]
  have ag : ∀ (n a : Nat), (∀ k, k < n → stdioFoot (a + k) ∧ ¬ outW (a + k)) →
      readLE (fillMem img dataList) a n = readLE m a n := fun n a h => readLE_agreeP hag n a h
  have F : ∀ a n, (0x8001b520 ≤ a ∧ a + n ≤ 0x8001b538 ∨ (0x8001b53c ≤ a ∧ a + n ≤ 0x8001b960) ∨
      (0x8001b970 ≤ a ∧ a + n ≤ 0x8001b990) ∨ (0x8001ba68 ≤ a ∧ a + n ≤ 0x8001bb20) ∨
      (0x8001bb32 ≤ a ∧ a + n ≤ 0x8001bb97) ∨ (0x8001bb98 ≤ a ∧ a + n ≤ 0x8001c168) ∨
      (0x8001bb28 ≤ a ∧ a + n ≤ 0x8001bb2c)) →
      ∀ k, k < n → stdioFoot (a + k) ∧ ¬ outW (a + k) := by
    intro a n h k hk; unfold stdioFoot InRange outW; omega
  have hmS : ∀ a, stdioFoot a → m[a]? = some (img' a) := hm
  have img_of : ∀ a n, (∀ k, k < n → stdioFoot (a + k)) → readLE m a n = some (imgLE img' a n) :=
    fun a n hS => readLE_of_img fun i hi => hmS _ (hS i hi)
  have hb0 : img' 0x8001bb30 = 0x0a#8 ∧ img' 0x8001bb31 = 0x20#8 := by
    simp only [imgLE, Nat.mul_zero, Nat.add_zero, Nat.reduceAdd] at hf
    have h0 := (img' 0x8001bb30).isLt; have h1 := (img' 2147597105).isLt
    constructor <;> apply BitVec.eq_of_toNat_eq
    · show (img' 0x8001bb30).toNat = 10; omega
    · show (img' 2147597105).toNat = 32; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    he.transport fun a ha => hag a (exitExtra_off ha), ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hc.impure
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hc.stdout
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hc.sinit
  · show readLE m 0x8001bb20 8 = _
    rw [img_of _ _ (fun k hk => by unfold stdioFoot InRange; omega), hp]; rfl
  · exact (ag 4 _ (F _ _ (by decide))).symm.trans hc.readCount
  · show readLE m 0x8001bb2c 4 = _
    rw [img_of _ _ (fun k hk => by unfold stdioFoot InRange; omega), hw]
  · show readLE m 0x8001bb30 2 = _
    rw [img_of _ _ (fun k hk => by unfold stdioFoot InRange; omega), hf]
  · rw [show consoleStdout + 16 = 0x8001bb30 by rfl, hmS _ (by unfold stdioFoot InRange; omega), hb0.1]
  · rw [show consoleStdout + 17 = 0x8001bb31 by rfl, hmS _ (by unfold stdioFoot InRange; omega), hb0.2]
  · exact (ag 2 _ (F _ _ (by decide))).symm.trans hc.fd
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hc.base
  · exact (ag 4 _ (F _ _ (by decide))).symm.trans hc.bufSize
  · exact (ag 4 _ (F _ _ (by decide))).symm.trans hc.lineBufSize
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hc.cookie
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hc.writer
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hc.lock
  · exact (ag 4 _ (F _ _ (by decide))).symm.trans hc.lockMode
  · exact ⟨_, hmS _ (by unfold stdioFoot InRange consoleBuf; omega)⟩
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hs
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hl.mbtowc
  · exact (ag 1 _ (F _ _ (by decide))).symm.trans hl.mbMax
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hl.decPoint
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hst.base
  · exact (ag 8 _ (F _ _ (by decide))).symm.trans hst.writer

end VsaIris.Stdio

import Vsa.Sim.RegPins
import Vsa.Sim.SlotFrame
import Vsa.Sim.PtrArith
import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.SnprintfSpec11
import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.CodeRangeInsert
import Vsa.Sim.Code.Strlen
import Vsa.Sim.Code.__locale_mb_cur_max
import Vsa.Sim.Code.__ascii_mbtowc
import Vsa.Sim.Code.Memset
import Vsa.Sim.Code._localeconv_r

/-!
# M3 Layer-3 — shared helpers for the svfprintf PROLOGUE + first-parse-pass segments

Pin-list surgery (`pins_cons_pro` / `pins_dropN_pro`), the `sp -= 592`
prologue round-trip, `Loaded`-survival for the callee code regions touched by
the prologue path (`memset`), and small value/guard folds shared by
`SnprintfSpec27`–`SnprintfSpec34`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Pin-list surgery -/

theorem pins_cons_pro {σ : MState} {R : Register} {v : RegisterType R} {L : List Pin}
    (h1 : σ.regs.get? R = some v) (h : PinsHold σ L) :
    PinsHold σ (⟨R, v⟩ :: L) := ⟨h1, h⟩

theorem pins_drop2_pro {σ : MState} {a b : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: L)) : PinsHold σ (a :: L) :=
  ⟨h.1, h.2.2⟩

theorem pins_drop3_pro {σ : MState} {a b c : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: L)) : PinsHold σ (a :: b :: L) :=
  ⟨h.1, h.2.1, h.2.2.2⟩

theorem pins_drop4_pro {σ : MState} {a b c d : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: L)) : PinsHold σ (a :: b :: c :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem pins_drop5_pro {σ : MState} {a b c d e : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: L)) : PinsHold σ (a :: b :: c :: d :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem pins_drop6_pro {σ : MState} {a b c d e f : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem pins_drop7_pro {σ : MState} {a b c d e f g : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem pins_drop8_pro {σ : MState} {a b c d e f g p8 : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2⟩

theorem pins_drop9_pro {σ : MState} {a b c d e f g p8 p9 : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop10_pro {σ : MState} {a b c d e f g p8 p9 p10 : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop11_pro {σ : MState} {a b c d e f g p8 p9 p10 p11 : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop12_pro {σ : MState} {a b c d e f g p8 p9 p10 p11 p12 : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12 :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop13_pro {σ : MState} {a b c d e f g p8 p9 p10 p11 p12 p13 : Pin} {L : List Pin}
    (h : PinsHold σ
      (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12 :: p13 :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop14_pro {σ : MState}
    {a b c d e f g p8 p9 p10 p11 p12 p13 p14 : Pin} {L : List Pin}
    (h : PinsHold σ
      (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12 :: p13 :: p14 :: L)) :
    PinsHold σ
      (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12 :: p13 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop15_pro {σ : MState}
    {a b c d e f g p8 p9 p10 p11 p12 p13 p14 p15 : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12
      :: p13 :: p14 :: p15 :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12
      :: p13 :: p14 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop16_pro {σ : MState}
    {a b c d e f g p8 p9 p10 p11 p12 p13 p14 p15 p16 : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12
      :: p13 :: p14 :: p15 :: p16 :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g :: p8 :: p9 :: p10 :: p11 :: p12
      :: p13 :: p14 :: p15 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩


theorem pins_drop17_pro {σ : MState}
    {q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 : Pin} {L : List Pin}
    (h : PinsHold σ (q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: L)) :
    PinsHold σ (q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop18_pro {σ : MState}
    {q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 : Pin} {L : List Pin}
    (h : PinsHold σ (q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: L)) :
    PinsHold σ (q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## Stack-frame arithmetic -/

/-- `v + sext 0x000 = v` (local twin of `SnprintfSpec21.sext0_add_rt`). -/
theorem sext0_add_pro (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]

/-- The svfprintf prologue round trip: `(vsp + 592) + sext(-592) = vsp`. -/
theorem sp_dec592_pro (vsp : BitVec 64) :
    (vsp + (592#64)) + sign_extend (m := 64) (0xdb0#12) = vsp :=
  add_cancel_pair _ _ _ (by apply BitVec.eq_of_toNat_eq; decide)

/-! ## `Loaded` survival for the prologue callees -/

theorem getElem?_insert_below_pro (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (v : BitVec 8) (hk : 0x80018000 ≤ k) (a : Nat) (ha : a < 0x80018000) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- `MemsetLoaded` (code at `[0x80006aec, 0x80006bc8)`) survives a byte store
at/above `0x80018000` (all prologue-path stores are stack stores with
`0x8001c000 ≤ sp`). -/
theorem memset_insert_pro (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80018000 ≤ k) (h : Vsa.Sim.Code.MemsetLoaded mem) :
    Vsa.Sim.Code.MemsetLoaded (mem.insert k v) := by
  unfold Vsa.Sim.Code.MemsetLoaded at h ⊢
  simp only [Vsa.Sim.Code.memsetChunk0, Vsa.Sim.Code.memsetChunk1,
    Vsa.Sim.Code.memsetChunk2, Vsa.Sim.Code.memsetChunk3] at h ⊢
  simp (disch := omega) only [getElem?_insert_below_pro mem k v hk]
  exact h

/-- `Vsa.Sim.Code.StrlenLoaded` (code at `[0x80006cf0, 0x80006dc4)`) survives stack stores. -/
theorem strlen_insert_pro (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80018000 ≤ k) (h : Vsa.Sim.Code.StrlenLoaded mem) : Vsa.Sim.Code.StrlenLoaded (mem.insert k v) := by
  unfold Vsa.Sim.Code.StrlenLoaded at h ⊢
  simp only [Vsa.Sim.Code.strlenChunk0, Vsa.Sim.Code.strlenChunk1,
    Vsa.Sim.Code.strlenChunk2, Vsa.Sim.Code.strlenChunk3] at h ⊢
  simp (disch := omega) only [getElem?_insert_below_pro mem k v hk]
  exact h

/-- `_localeconv_rLoaded` (2 instructions at `0x80010258`) survives stack stores. -/
theorem localeconv_insert_pro (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80018000 ≤ k) (h : Vsa.Sim.Code._localeconv_rLoaded mem) :
    Vsa.Sim.Code._localeconv_rLoaded (mem.insert k v) := by
  unfold Vsa.Sim.Code._localeconv_rLoaded at h ⊢
  simp only [Vsa.Sim.Code._localeconv_rChunk0] at h ⊢
  simp (disch := omega) only [getElem?_insert_below_pro mem k v hk]
  exact h

/-- `__locale_mb_cur_maxLoaded` (2 instructions at `0x80010234`) survives stack stores. -/
theorem localemb_insert_pro (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80018000 ≤ k) (h : Vsa.Sim.Code.__locale_mb_cur_maxLoaded mem) :
    Vsa.Sim.Code.__locale_mb_cur_maxLoaded (mem.insert k v) := by
  unfold Vsa.Sim.Code.__locale_mb_cur_maxLoaded at h ⊢
  simp only [Vsa.Sim.Code.__locale_mb_cur_maxChunk0] at h ⊢
  simp (disch := omega) only [getElem?_insert_below_pro mem k v hk]
  exact h

/-- `__ascii_mbtowcLoaded` (code at `[0x80012268, 0x800122d0)`) survives stack stores. -/
theorem amb_insert_pro (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80018000 ≤ k) (h : Vsa.Sim.Code.__ascii_mbtowcLoaded mem) :
    Vsa.Sim.Code.__ascii_mbtowcLoaded (mem.insert k v) := by
  unfold Vsa.Sim.Code.__ascii_mbtowcLoaded at h ⊢
  simp only [Vsa.Sim.Code.__ascii_mbtowcChunk0, Vsa.Sim.Code.__ascii_mbtowcChunk1] at h ⊢
  simp (disch := omega) only [getElem?_insert_below_pro mem k v hk]
  exact h

section
variable (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)

/-- 8-byte-store survival wrappers over the byte-insert lemmas above. -/
theorem strlen_w8_pro (d : BitVec (8 * 8)) (ha : 0x80018000 ≤ a) (h : Vsa.Sim.Code.StrlenLoaded mem) :
    Vsa.Sim.Code.StrlenLoaded (writeMap8 mem a d) :=
  strlen_insert_pro _ _ _ (by omega) (strlen_insert_pro _ _ _ (by omega)
    (strlen_insert_pro _ _ _ (by omega) (strlen_insert_pro _ _ _ (by omega)
    (strlen_insert_pro _ _ _ (by omega) (strlen_insert_pro _ _ _ (by omega)
    (strlen_insert_pro _ _ _ (by omega) (strlen_insert_pro _ _ _ (by omega) h)))))))

theorem localeconv_w8_pro (d : BitVec (8 * 8)) (ha : 0x80018000 ≤ a)
    (h : Vsa.Sim.Code._localeconv_rLoaded mem) :
    Vsa.Sim.Code._localeconv_rLoaded (writeMap8 mem a d) :=
  localeconv_insert_pro _ _ _ (by omega) (localeconv_insert_pro _ _ _ (by omega)
    (localeconv_insert_pro _ _ _ (by omega) (localeconv_insert_pro _ _ _ (by omega)
    (localeconv_insert_pro _ _ _ (by omega) (localeconv_insert_pro _ _ _ (by omega)
    (localeconv_insert_pro _ _ _ (by omega) (localeconv_insert_pro _ _ _ (by omega) h)))))))

theorem localemb_w8_pro (d : BitVec (8 * 8)) (ha : 0x80018000 ≤ a)
    (h : Vsa.Sim.Code.__locale_mb_cur_maxLoaded mem) :
    Vsa.Sim.Code.__locale_mb_cur_maxLoaded (writeMap8 mem a d) :=
  localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
    (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
    (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
    (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega) h)))))))

theorem localemb_w4_pro (d : BitVec (8 * 4)) (ha : 0x80018000 ≤ a)
    (h : Vsa.Sim.Code.__locale_mb_cur_maxLoaded mem) :
    Vsa.Sim.Code.__locale_mb_cur_maxLoaded (writeMap4 mem a d) :=
  localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
    (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega) h)))

theorem memset_w8_pro (d : BitVec (8 * 8)) (ha : 0x80018000 ≤ a)
    (h : Vsa.Sim.Code.MemsetLoaded mem) : Vsa.Sim.Code.MemsetLoaded (writeMap8 mem a d) :=
  memset_insert_pro _ _ _ (by omega) (memset_insert_pro _ _ _ (by omega)
    (memset_insert_pro _ _ _ (by omega) (memset_insert_pro _ _ _ (by omega)
    (memset_insert_pro _ _ _ (by omega) (memset_insert_pro _ _ _ (by omega)
    (memset_insert_pro _ _ _ (by omega) (memset_insert_pro _ _ _ (by omega) h)))))))

theorem memset_w4_pro (d : BitVec (8 * 4)) (ha : 0x80018000 ≤ a)
    (h : Vsa.Sim.Code.MemsetLoaded mem) : Vsa.Sim.Code.MemsetLoaded (writeMap4 mem a d) :=
  memset_insert_pro _ _ _ (by omega) (memset_insert_pro _ _ _ (by omega)
    (memset_insert_pro _ _ _ (by omega) (memset_insert_pro _ _ _ (by omega) h)))

theorem amb_w8_pro (d : BitVec (8 * 8)) (ha : 0x80018000 ≤ a)
    (h : Vsa.Sim.Code.__ascii_mbtowcLoaded mem) :
    Vsa.Sim.Code.__ascii_mbtowcLoaded (writeMap8 mem a d) :=
  amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
    (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
    (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
    (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega) h)))))))

theorem amb_w4_pro (d : BitVec (8 * 4)) (ha : 0x80018000 ≤ a)
    (h : Vsa.Sim.Code.__ascii_mbtowcLoaded mem) :
    Vsa.Sim.Code.__ascii_mbtowcLoaded (writeMap4 mem a d) :=
  amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
    (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega) h)))

theorem svf_w4_pro (d : BitVec (8 * 4)) (ha : 0x80018000 ≤ a)
    (h : Vsa.Sim.Code.SvfprintfSliceLoaded mem) :
    Vsa.Sim.Code.SvfprintfSliceLoaded (writeMap4 mem a d) :=
  svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _ (by omega)
    (svfprintfSlice_insert_sn4 _ _ _ (by omega)
      (svfprintfSlice_insert_sn4 _ _ _ (by omega) h)))

end

/-- Reads outside a 4-byte `writeMap4` window are unchanged (two-sided twin of
`getElem?_writeMap8_out`). -/
theorem getElem?_writeMap4_out_pro (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 4)) (a : Nat) (ha : a < k ∨ k + 4 ≤ a) :
    (writeMap4 mem k d)[a]? = mem[a]? := by
  show ((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- Transport a `SlotHolds` across any memory transition that agrees pointwise
on the slot's 8-byte window (glue form for the segment `hag` clauses). -/
theorem slotHolds_agree_pro (base : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem mem' : Std.ExtHashMap Nat (BitVec 8))
    (hf : ∀ a : Nat, (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat ≤ a →
      a < (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 →
      mem'[a]? = mem[a]?)
    (h : SlotHolds base off v mem) : SlotHolds base off v mem' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(hf _ (by omega) (by omega)).trans h0, (hf _ (by omega) (by omega)).trans h1,
    (hf _ (by omega) (by omega)).trans h2, (hf _ (by omega) (by omega)).trans h3,
    (hf _ (by omega) (by omega)).trans h4, (hf _ (by omega) (by omega)).trans h5,
    (hf _ (by omega) (by omega)).trans h6, (hf _ (by omega) (by omega)).trans h7⟩

/-! ## Value / guard folds -/

/-- `subw` of two equal operands is zero. -/
theorem subw_self_pro (v : BitVec 64) :
    (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb v 31 0) - (Sail.BitVec.extractLsb v 31 0)) : BitVec 64)
      = 0#64 := by
  rw [BitVec.sub_self]
  apply BitVec.eq_of_toNat_eq
  simp only [sign_extend, Sail.BitVec.signExtend]
  decide

/-- `beq` on distinct `toNat`s is false. -/
theorem beq64_false_pro (a b : BitVec 64) (h : a.toNat ≠ b.toNat) :
    (a == b) = false := by
  rw [beq_eq_false_iff_ne]
  intro he; exact h (by rw [he])

end Vsa.Sim

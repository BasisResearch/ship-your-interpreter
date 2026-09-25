import VsaIris.Interp.StrlenRun
import Vsa.Sim.MemcpySpec
import Vsa.Sim.PinW

/-!
# `strcpy` as a symbolic run over a persistent string into an owned buffer

The whole of newlib's `strcpy` (`0x80006dc4`) as one `SW` run
(`StrCode.lean`): the source is the string's bytes `[s, s + len]` (the data
view, persistent), the destination an owned buffer `[d, d + N)`, `N ≥ len + 1`.

* misaligned (`(d | s) & 7 ≠ 0`): the byte loop copies `len + 1` bytes;
* aligned: the word loop loads whole words (`sr_havoc`: the last one may
  reach up to seven bytes past the NUL, nobody's bytes) and stores the words
  before the NUL's; the byte tail loads up to two bytes ahead of the byte it
  stores (again possibly past the NUL, again `sr_havoc`) and stores bytes up
  to the NUL only.

Every store lands in `[d, d + len]`; the run ends with those bytes holding
the string (`CpyEnd`). Stores need `tohostAddr + 16 ≤ d` (VSA's store facts,
`BlockMem.MemFacts`).
-/

namespace VsaIris.Interp.StrLeaf

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Inst.Strlen
open Vsa.Sim Vsa.MemRepr
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `strcpy`'s end: back at `r`, `a0 = d`, and `[d, d + len]` holds the string. -/
def CpyEnd (r d s : BitVec 64) (len : Nat) (bv : Nat → BitVec 8) (rv : Nat → BitVec 64)
    (mv : Nat → BitVec 8) : Prop :=
  rv 32 = r ∧ rv 1 = r ∧ rv 10 = d ∧ ∀ k, k ≤ len → mv (d.toNat + k) = bv (s.toNat + k)

/-- **The side conditions of a `strcpy` run.** -/
structure CCtx (live : Nat → Prop) (d s r : BitVec 64) (len : Nat) (bv : Nat → BitVec 8)
    (N : Nat) : Prop where
  src : LCtx live s r len bv
  dlo : tohostAddr + 16 ≤ d.toNat
  dhi : d.toNat + N ≤ 0x100000000
  room : len + 1 ≤ N

/-- `strcpy`'s run from the string `[s, s + len]` into the owned `[d, d + N)`. -/
abbrev CW (live : Nat → Prop) (d s r : BitVec 64) (len : Nat) (bv : Nat → BitVec 8) (N : Nat) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SW live (strText s.toNat len bv) (InExt (d.toNat, N)) (CpyEnd r d s len bv)

/-- The destination's first `k` bytes hold the string's. -/
def Pfx (d s : Nat) (bv : Nat → BitVec 8) (Mt : Mem) (k : Nat) : Prop :=
  ∀ j, j < k → imgM Mt (d + j) = bv (s + j)

variable {live : Nat → Prop} {d s r : BitVec 64} {len : Nat} {bv : Nat → BitVec 8} {N : Nat}

/-! ## Bytes a store leaves -/

theorem imgM_sb1 (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgM (writeLog Mt [(a, 1, v)]) a = sbData v := by
  unfold imgM writeLog
  simp only [List.foldl, applyW, Std.ExtHashMap.getElem?_insert]
  simp

theorem imgM_sd8 (Mt : Mem) (a : Nat) (v : BitVec 64) (i : Nat) (hi : i < 8) :
    imgM (writeLog Mt [(a, 8, v)]) (a + i) = (sdData_val v).extractLsb' (8 * i) 8 := by
  unfold imgM writeLog
  simp only [List.foldl, applyW, writeMap8, Std.ExtHashMap.getElem?_insert]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first
    | omega
    | simp

theorem imgM_sb_zext (Mt : Mem) (a : Nat) (b : BitVec 8) :
    imgM (writeLog Mt [(a, 1, zero_extend (m := 64) b)]) a = b := by
  rw [imgM_sb1]; exact sbData_zext b

theorem Pfx.store1 {Mt : Mem} {k : Nat} (h : Pfx d.toNat s.toNat bv Mt k) {v : BitVec 64}
    (hv : sbData v = bv (s.toNat + k)) :
    Pfx d.toNat s.toNat bv (writeLog Mt [(d.toNat + k, 1, v)]) (k + 1) := by
  intro j hj
  by_cases hjk : j = k
  · subst hjk; rw [imgM_sb1]; exact hv
  · rw [imgM_store_miss _ _ (by omega)]; exact h j (by omega)

theorem Pfx.mono {Mt : Mem} {k k' : Nat} (h : Pfx d.toNat s.toNat bv Mt k) (hk : k' ≤ k) :
    Pfx d.toNat s.toNat bv Mt k' := fun j hj => h j (by omega)

/-! ## The end -/

theorem cpyEnd (c : CCtx live d s r len bv N) {R : Nat → BitVec 64} {Mt : Mem}
    (hR1 : R 1 = r) (h10 : R 10 = d) (hp : Pfx d.toNat s.toNat bv Mt (len + 1)) :
    CW live d s r len bv N r R Mt :=
  sr_done fun _ _ hm => ⟨hm.pc, by rw [hm.regs 1 (by decide) (by decide), hR1],
    by rw [hm.regs 10 (by decide) (by decide), h10], fun k hk => by
      have hr := c.room
      rw [hm.img _ ⟨by simp, by simp; omega⟩]; exact hp k (by omega)⟩

/-! ## Arithmetic -/

theorem sext_imm (imm : BitVec 12) (j : Nat) (h : (sign_extend (m := 64) imm : BitVec 64) = BitVec.ofNat 64 j)
    (x : BitVec 64) (k : Nat) :
    (x + BitVec.ofNat 64 k) + sign_extend (m := 64) imm = x + BitVec.ofNat 64 (k + j) := by
  rw [h, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem sext1 : (sign_extend (m := 64) (0x001#12) : BitVec 64) = BitVec.ofNat 64 1 := by
  apply BitVec.eq_of_toNat_eq; decide

theorem inc_dec (x : BitVec 64) :
    (x + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0xfff#12) = x := by
  rw [BitVec.add_assoc,
    show (sign_extend (m := 64) (0x001#12) : BitVec 64) + sign_extend (m := 64) (0xfff#12) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]

theorem CCtx.ptrd (c : CCtx live d s r len bv N) {k : Nat} (hk : k ≤ N) :
    (d + BitVec.ofNat 64 k).toNat = d.toNat + k :=
  ptrN d k (by have := c.dhi; omega)

theorem CCtx.ptrs (c : CCtx live d s r len bv N) {k : Nat} (hk : k ≤ len + 8) :
    (s + BitVec.ofNat 64 k).toNat = s.toNat + k :=
  ptrN s k (by have := c.src.regions.nowrap; omega)

theorem CCtx.stb (c : CCtx live d s r len bv N) {k : Nat} (hk : k < N) :
    StOKb (d.toNat + k) := by
  have := c.dlo; have := c.dhi
  exact ⟨by unfold tohostAddr at *; omega, by omega, by omega⟩

theorem CCtx.inS (c : CCtx live d s r len bv N) {k w : Nat} (hk : k + w ≤ N) :
    ∀ b ∈ accAddrs (d.toNat + k) w, InExt (d.toNat, N) b := by
  intro b hb
  have := of_mem_accAddrs hb
  exact ⟨by simp; omega, by simp; omega⟩

/-! ## The byte loop `0x80006e7c … 0x80006e94` (misaligned) -/

/-- At the byte-loop head `0x80006e80`, `i` bytes copied. -/
structure ByteAt (d s r : BitVec 64) (len : Nat) (bv : Nat → BitVec 8) (i : Nat)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  ra : R 1 = r
  a0 : R 10 = d
  a1 : R 11 = s + BitVec.ofNat 64 i
  a5 : R 15 = d + BitVec.ofNat 64 i
  ile : i ≤ len
  pfx : Pfx d.toNat s.toNat bv Mt i

theorem byteRun (c : CCtx live d s r len bv N) :
    ∀ (n i : Nat) (R : Nat → BitVec 64) (Mt : Mem), len = i + n →
      ByteAt d s r len bv i R Mt → CW live d s r len bv N 0x80006e80#64 R Mt := by
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro i R Mt hn h
    have hile := h.ile
    have hroom := c.room
    have ha : ((R 11) + sign_extend (m := 64) (0x000#12)).toNat = s.toNat + i := by
      rw [sext0_add, h.a1]; exact c.ptrs (by omega)
    have hd : ((R 15 + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0xfff#12)).toNat =
        d.toNat + i := by
      rw [inc_dec, h.a5]; exact c.ptrd (by omega)
    refine slH_80006e80 c.src.code (by rw [ha]; exact ldok c.src (by omega)) fun f hf => ?_
    have hb : f (s.toNat + i) = bv (s.toNat + i) := agree_at hf h.ile
    refine sl_80006e84 c.src.code (sl_80006e88 c.src.code (sl_80006e8c c.src.code ?_ ?_ ?_))
    · simp (disch := decide) only [upd_same, upd_other]; rw [hd]; exact c.stb (by omega)
    · simp (disch := decide) only [upd_same, upd_other]; rw [hd]; exact c.inS (by omega)
    simp (disch := decide) only [upd_same, upd_other]
    rw [hd, ha, ldvf_lbu, hb]
    have hp := h.pfx.store1 (v := zero_extend (m := 64) (bv (s.toNat + i))) (sbData_zext _)
    refine sl_80006e90 c.src.code (fun hnz => ?_) (fun hz => ?_)
    all_goals first
      | (simp (disch := decide) only [upd_same, upd_other] at hnz)
      | (simp (disch := decide) only [upd_same, upd_other] at hz)
  · exact absurd ((byte_zero_iff c.src hile).1 ((zext_eq_zero _).1 (by
      rw [zext_eq_zero]; exact (byte_zero_iff c.src hile).2 (by omega)))) (by
        intro _; exact hnz ((zext_eq_zero _).2 ((byte_zero_iff c.src hile).2 (by omega))))
  · have hi : i = len := (byte_zero_iff c.src hile).1 ((zext_eq_zero _).1 (Classical.not_not.1 hz))
    subst hi
    refine sl_80006e94 c.src.code ?_ ?_
    · simp (disch := decide) only [upd_same, upd_other]; rw [h.ra]; exact c.src.retAlign
    · have e1 : ∀ v1 v2 v3, upd (upd (upd R 14 v1) 15 v2) 11 v3 1 = r := by
        intro v1 v2 v3; simp (disch := decide) only [upd_other]; exact h.ra
      rw [e1]
      exact cpyEnd c (e1 _ _ _) (by simp (disch := decide) only [upd_other]; exact h.a0) hp
  · have hlt : i < len := by
      refine Nat.lt_of_le_of_ne hile fun e => hnz ?_
      rw [zext_eq_zero]; exact (byte_zero_iff c.src hile).2 e
    refine ih (i + 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, by omega, hp⟩
    all_goals simp (disch := decide) only [upd_same, upd_other]
    · exact h.ra
    · exact h.a0
    · rw [h.a1]; exact Strlen.a4_incr1 s i
    · rw [h.a5]; exact Strlen.a4_incr1 d i
  · have hi : i = len := (byte_zero_iff c.src hile).1 ((zext_eq_zero _).1 (Classical.not_not.1 hz))
    omega

theorem sx0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sx1 : (sign_extend (m := 64) (0x001#12) : BitVec 64) = BitVec.ofNat 64 1 := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sx2 : (sign_extend (m := 64) (0x002#12) : BitVec 64) = BitVec.ofNat 64 2 := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sx3 : (sign_extend (m := 64) (0x003#12) : BitVec 64) = BitVec.ofNat 64 3 := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sx4 : (sign_extend (m := 64) (0x004#12) : BitVec 64) = BitVec.ofNat 64 4 := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sx5 : (sign_extend (m := 64) (0x005#12) : BitVec 64) = BitVec.ofNat 64 5 := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sx6 : (sign_extend (m := 64) (0x006#12) : BitVec 64) = BitVec.ofNat 64 6 := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sx7 : (sign_extend (m := 64) (0x007#12) : BitVec 64) = BitVec.ofNat 64 7 := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## The byte tail `0x80006e24 … 0x80006e9c` (aligned) -/

theorem tailRet (c : CCtx live d s r len bv N) {R : Nat → BitVec 64} {Mt : Mem}
    (hra : R 1 = r) (h10 : R 10 = d) (hp : Pfx d.toNat s.toNat bv Mt (len + 1)) :
    CW live d s r len bv N 0x80006e78#64 R Mt := by
  refine sl_80006e78 c.src.code (by rw [hra]; exact c.src.retAlign) ?_
  rw [hra]; exact cpyEnd c hra h10 hp

/-- At the byte tail `0x80006e24`: the word at `s + t` holds the NUL. -/
structure CTail (d s r : BitVec 64) (len : Nat) (bv : Nat → BitVec 8) (t : Nat)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  ra : R 1 = r
  a0 : R 10 = d
  a1 : R 11 = s + BitVec.ofNat 64 t
  a2 : R 12 = d + BitVec.ofNat 64 t
  lo : t ≤ len
  hi : len < t + 8
  pfx : Pfx d.toNat s.toNat bv Mt t

theorem tailCpy (c : CCtx live d s r len bv N) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h : CTail d s r len bv t R Mt) : CW live d s r len bv N 0x80006e24#64 R Mt := by
  have hlo := h.lo; have hhi := h.hi; have hroom := c.room; have hdhi := c.dhi
  have hA : ∀ (k : Nat) (imm : BitVec 12), (sign_extend (m := 64) imm : BitVec 64) = BitVec.ofNat 64 k →
      k ≤ 7 → ((R 11) + sign_extend (m := 64) imm).toNat = s.toNat + (t + k) := by
    intro k imm hi hk; rw [h.a1, sext_imm imm k hi]; exact c.ptrs (by omega)
  have hD : ∀ (k : Nat) (imm : BitVec 12), (sign_extend (m := 64) imm : BitVec 64) = BitVec.ofNat 64 k →
      k ≤ 7 → ((R 12) + sign_extend (m := 64) imm).toNat = d.toNat + (t + k) := by
    intro k imm hi hk; rw [h.a2, sext_imm imm k hi]; exact ptrN d (t + k) (by omega)
  have hLd : ∀ k, k ≤ 7 → LdOK (s.toNat + (t + k)) 1 := fun k hk => ldok c.src (by omega)
  refine slH_80006e24 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hA 0 _ sx0 (by omega)]; exact hLd 0 (by omega)) fun f0 hf0 => ?_
  try simp (disch := decide) only [upd_same, upd_other]
  rw [hA 0 _ sx0 (by omega), ldvf_lbu]
  refine slH_80006e28 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hA 1 _ sx1 (by omega)]; exact hLd 1 (by omega)) fun f1 hf1 => ?_
  try simp (disch := decide) only [upd_same, upd_other]
  rw [hA 1 _ sx1 (by omega), ldvf_lbu]
  refine slH_80006e2c c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hA 2 _ sx2 (by omega)]; exact hLd 2 (by omega)) fun f2 hf2 => ?_
  try simp (disch := decide) only [upd_same, upd_other]
  rw [hA 2 _ sx2 (by omega), ldvf_lbu]
  have hle0 : t + 0 ≤ len := by omega
  refine sl_80006e30 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 0 _ sx0 (by omega)]; exact c.stb (by omega)) (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 0 _ sx0 (by omega)]; exact c.inS (by omega)) ?_
  simp (disch := decide) only [upd_same, upd_other]
  rw [hD 0 _ sx0 (by omega)]
  have hp0 := h.pfx.store1 (k := t + 0) (v := zero_extend (m := 64) (f0 (s.toNat + (t + 0)))) (by rw [sbData_zext, agree_at hf0 hle0])
  refine sl_80006e34 c.src.code (fun hz => ?_) (fun hnz => ?_)
  · simp (disch := decide) only [upd_same, upd_other] at hz
    rw [zext_eq_zero, agree_at hf0 hle0, byte_zero_iff c.src hle0] at hz
    exact tailRet c (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.ra) (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.a0) (hp0.mono (by omega))
  simp (disch := decide) only [upd_same, upd_other] at hnz
  rw [zext_eq_zero, agree_at hf0 hle0, byte_zero_iff c.src hle0] at hnz
  have hle1 : t + 1 ≤ len := by omega
  refine sl_80006e38 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 1 _ sx1 (by omega)]; exact c.stb (by omega)) (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 1 _ sx1 (by omega)]; exact c.inS (by omega)) ?_
  simp (disch := decide) only [upd_same, upd_other]
  rw [hD 1 _ sx1 (by omega)]
  have hp1 := hp0.store1 (k := t + 1) (v := zero_extend (m := 64) (f1 (s.toNat + (t + 1)))) (by rw [sbData_zext, agree_at hf1 hle1])
  refine sl_80006e3c c.src.code (fun hz => ?_) (fun hnz => ?_)
  · simp (disch := decide) only [upd_same, upd_other] at hz
    rw [zext_eq_zero, agree_at hf1 hle1, byte_zero_iff c.src hle1] at hz
    exact tailRet c (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.ra) (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.a0) (hp1.mono (by omega))
  simp (disch := decide) only [upd_same, upd_other] at hnz
  rw [zext_eq_zero, agree_at hf1 hle1, byte_zero_iff c.src hle1] at hnz
  refine slH_80006e40 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hA 3 _ sx3 (by omega)]; exact hLd 3 (by omega)) fun f3 hf3 => ?_
  try simp (disch := decide) only [upd_same, upd_other]
  rw [hA 3 _ sx3 (by omega), ldvf_lbu]
  have hle2 : t + 2 ≤ len := by omega
  refine sl_80006e44 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 2 _ sx2 (by omega)]; exact c.stb (by omega)) (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 2 _ sx2 (by omega)]; exact c.inS (by omega)) ?_
  simp (disch := decide) only [upd_same, upd_other]
  rw [hD 2 _ sx2 (by omega)]
  have hp2 := hp1.store1 (k := t + 2) (v := zero_extend (m := 64) (f2 (s.toNat + (t + 2)))) (by rw [sbData_zext, agree_at hf2 hle2])
  refine sl_80006e48 c.src.code (fun hz => ?_) (fun hnz => ?_)
  · simp (disch := decide) only [upd_same, upd_other] at hz
    rw [zext_eq_zero, agree_at hf2 hle2, byte_zero_iff c.src hle2] at hz
    exact tailRet c (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.ra) (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.a0) (hp2.mono (by omega))
  simp (disch := decide) only [upd_same, upd_other] at hnz
  rw [zext_eq_zero, agree_at hf2 hle2, byte_zero_iff c.src hle2] at hnz
  refine slH_80006e4c c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hA 4 _ sx4 (by omega)]; exact hLd 4 (by omega)) fun f4 hf4 => ?_
  try simp (disch := decide) only [upd_same, upd_other]
  rw [hA 4 _ sx4 (by omega), ldvf_lbu]
  have hle3 : t + 3 ≤ len := by omega
  refine sl_80006e50 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 3 _ sx3 (by omega)]; exact c.stb (by omega)) (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 3 _ sx3 (by omega)]; exact c.inS (by omega)) ?_
  simp (disch := decide) only [upd_same, upd_other]
  rw [hD 3 _ sx3 (by omega)]
  have hp3 := hp2.store1 (k := t + 3) (v := zero_extend (m := 64) (f3 (s.toNat + (t + 3)))) (by rw [sbData_zext, agree_at hf3 hle3])
  refine sl_80006e54 c.src.code (fun hz => ?_) (fun hnz => ?_)
  · simp (disch := decide) only [upd_same, upd_other] at hz
    rw [zext_eq_zero, agree_at hf3 hle3, byte_zero_iff c.src hle3] at hz
    exact tailRet c (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.ra) (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.a0) (hp3.mono (by omega))
  simp (disch := decide) only [upd_same, upd_other] at hnz
  rw [zext_eq_zero, agree_at hf3 hle3, byte_zero_iff c.src hle3] at hnz
  refine slH_80006e58 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hA 5 _ sx5 (by omega)]; exact hLd 5 (by omega)) fun f5 hf5 => ?_
  try simp (disch := decide) only [upd_same, upd_other]
  rw [hA 5 _ sx5 (by omega), ldvf_lbu]
  have hle4 : t + 4 ≤ len := by omega
  refine sl_80006e5c c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 4 _ sx4 (by omega)]; exact c.stb (by omega)) (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 4 _ sx4 (by omega)]; exact c.inS (by omega)) ?_
  simp (disch := decide) only [upd_same, upd_other]
  rw [hD 4 _ sx4 (by omega)]
  have hp4 := hp3.store1 (k := t + 4) (v := zero_extend (m := 64) (f4 (s.toNat + (t + 4)))) (by rw [sbData_zext, agree_at hf4 hle4])
  refine sl_80006e60 c.src.code (fun hz => ?_) (fun hnz => ?_)
  · simp (disch := decide) only [upd_same, upd_other] at hz
    rw [zext_eq_zero, agree_at hf4 hle4, byte_zero_iff c.src hle4] at hz
    exact tailRet c (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.ra) (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.a0) (hp4.mono (by omega))
  simp (disch := decide) only [upd_same, upd_other] at hnz
  rw [zext_eq_zero, agree_at hf4 hle4, byte_zero_iff c.src hle4] at hnz
  refine slH_80006e64 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hA 6 _ sx6 (by omega)]; exact hLd 6 (by omega)) fun f6 hf6 => ?_
  try simp (disch := decide) only [upd_same, upd_other]
  rw [hA 6 _ sx6 (by omega), ldvf_lbu]
  have hle5 : t + 5 ≤ len := by omega
  refine sl_80006e68 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 5 _ sx5 (by omega)]; exact c.stb (by omega)) (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 5 _ sx5 (by omega)]; exact c.inS (by omega)) ?_
  simp (disch := decide) only [upd_same, upd_other]
  rw [hD 5 _ sx5 (by omega)]
  have hp5 := hp4.store1 (k := t + 5) (v := zero_extend (m := 64) (f5 (s.toNat + (t + 5)))) (by rw [sbData_zext, agree_at hf5 hle5])
  refine sl_80006e6c c.src.code (fun hz => ?_) (fun hnz => ?_)
  · simp (disch := decide) only [upd_same, upd_other] at hz
    rw [zext_eq_zero, agree_at hf5 hle5, byte_zero_iff c.src hle5] at hz
    exact tailRet c (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.ra) (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.a0) (hp5.mono (by omega))
  simp (disch := decide) only [upd_same, upd_other] at hnz
  rw [zext_eq_zero, agree_at hf5 hle5, byte_zero_iff c.src hle5] at hnz
  have hle6 : t + 6 ≤ len := by omega
  refine sl_80006e70 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 6 _ sx6 (by omega)]; exact c.stb (by omega)) (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 6 _ sx6 (by omega)]; exact c.inS (by omega)) ?_
  simp (disch := decide) only [upd_same, upd_other]
  rw [hD 6 _ sx6 (by omega)]
  have hp6 := hp5.store1 (k := t + 6) (v := zero_extend (m := 64) (f6 (s.toNat + (t + 6)))) (by rw [sbData_zext, agree_at hf6 hle6])
  refine sl_80006e74 c.src.code (fun hnz => ?_) (fun hz => ?_)
  · simp (disch := decide) only [upd_same, upd_other] at hnz
    rw [Ne, zext_eq_zero, agree_at hf6 hle6, byte_zero_iff c.src hle6] at hnz
    refine sl_80006e98 c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 7 _ sx7 (by omega)]; exact c.stb (by omega)) (by (try simp (disch := decide) only [upd_same, upd_other]); rw [hD 7 _ sx7 (by omega)]; exact c.inS (by omega)) ?_
    simp (disch := decide) only [upd_same, upd_other]
    rw [hD 7 _ sx7 (by omega)]
    have hp7 := hp6.store1 (k := t + 7) (v := 0#64) (by rw [show t + 7 = len by omega, c.src.str.nul]; rfl)
    refine sl_80006e9c c.src.code (by (try simp (disch := decide) only [upd_same, upd_other]); rw [h.ra]; exact c.src.retAlign) ?_
    simp (disch := decide) only [upd_same, upd_other]
    rw [h.ra]
    exact cpyEnd c (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.ra) (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.a0) (hp7.mono (by omega))
  · simp (disch := decide) only [upd_same, upd_other] at hz
    rw [Ne, zext_eq_zero, agree_at hf6 hle6, byte_zero_iff c.src hle6, Classical.not_not] at hz
    exact tailRet c (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.ra) (by (try simp (disch := decide) only [upd_same, upd_other]); exact h.a0) (hp6.mono (by omega))



/-! ## The word loop `0x80006dd0 … 0x80006e20` (aligned) -/

theorem Pfx.store8 {Mt : Mem} {t : Nat} (h : Pfx d.toNat s.toNat bv Mt t) {w : BitVec 64}
    (hw : ∀ i, i < 8 → w.extractLsb' (8 * i) 8 = bv (s.toNat + (t + i))) :
    Pfx d.toNat s.toNat bv (writeLog Mt [(d.toNat + t, 8, w)]) (t + 8) := by
  intro j hj
  by_cases hjt : j < t
  · rw [imgM_store_miss _ _ (by omega)]; exact h j hjt
  · have e : d.toNat + j = d.toNat + t + (j - t) := by omega
    rw [e, imgM_sd8 _ _ _ _ (by omega), sdData_val_id, hw _ (by omega),
      show t + (j - t) = j by omega]

/-- The bytes of a word loaded before the NUL. -/
theorem word_bytes {P : BitVec 64} {f : Nat → BitVec 8}
    (hf : ∀ q ∈ strText P.toNat len bv, f q.1 = q.2) {t : Nat} (ht : t + 8 ≤ len) :
    ∀ i, i < 8 → (ldvf .ld f (P.toNat + t)).extractLsb' (8 * i) 8 = bv (P.toNat + (t + i)) := by
  intro i hi
  rw [ldvf_ld_byte f _ _ hi, Nat.add_assoc, agree_at hf (by omega)]

theorem or_aligned {x y : BitVec 64}
    (h : ((x ||| y) &&& sign_extend (m := 64) (0x007#12)) = 0#64) : x.toNat % 8 = 0 := by
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_or,
    show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.or_mod_two_pow] at h2
  exact (Nat.or_eq_zero_iff.mp h2).1

/-- At the word-loop head `0x80006e00`: the word at `s + t` (before the NUL)
is in `a4`, the stored prefix is `t` bytes. -/
structure CWord (d s r : BitVec 64) (len : Nat) (bv : Nat → BitVec 8) (t : Nat)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  ra : R 1 = r
  a0 : R 10 = d
  a1 : R 11 = s + BitVec.ofNat 64 t
  a2 : R 12 = d + BitVec.ofNat 64 t
  a3 : R 13 = magic7f
  a4 : ∀ i, i < 8 → (R 14).extractLsb' (8 * i) 8 = bv (s.toNat + (t + i))
  a6 : R 16 = BitVec.allOnes 64
  hi : t + 8 ≤ len
  al : (d.toNat + t) % 8 = 0
  pfx : Pfx d.toNat s.toNat bv Mt t

theorem wordCpy (c : CCtx live d s r len bv N) :
    ∀ (n t : Nat) (R : Nat → BitVec 64) (Mt : Mem), len < t + 8 * n + 8 →
      CWord d s r len bv t R Mt → CW live d s r len bv N 0x80006e00#64 R Mt := by
  intro n
  induction n with
  | zero => intro t R Mt hn h; have := h.hi; omega
  | succ n ih =>
    intro t R Mt hn h
    have hle := h.hi; have hroom := c.room; have hdhi := c.dhi; have hdlo := c.dlo
    have hnw := c.src.regions.nowrap
    have hD : ((R 12) + sign_extend (m := 64) (0x000#12)).toNat = d.toNat + t := by
      rw [sext0_add, h.a2]; exact ptrN d t (by omega)
    have hA : ((R 11) + sign_extend (m := 64) (0x008#12) + sign_extend (m := 64) (0x000#12)).toNat =
        s.toNat + (t + 8) := by
      rw [sext0_add, h.a1, a4_plus8]; exact ptrN s (t + 8) (by omega)
    have hp := h.pfx.store8 (w := R 14) h.a4
    refine sl_80006e00 c.src.code (sl_80006e04 c.src.code ?_ ?_ ?_)
    · simp (disch := decide) only [upd_other]; rw [hD]
      exact ⟨by unfold tohostAddr at *; omega, by omega, by omega, h.al⟩
    · simp (disch := decide) only [upd_other]; rw [hD]; exact c.inS (by omega)
    simp (disch := decide) only [upd_other]
    rw [hD]
    refine slH_80006e08 c.src.code (by
      simp (disch := decide) only [upd_same, upd_other]; rw [hA]; exact ldok c.src (by omega))
      fun f hf => ?_
    simp (disch := decide) only [upd_same, upd_other]
    rw [hA]
    have htest := word_test c.src hf (t := t + 8) hle
    refine sl_80006e0c c.src.code (sl_80006e10 c.src.code (sl_80006e14 c.src.code
      (sl_80006e18 c.src.code (sl_80006e1c c.src.code (sl_80006e20 c.src.code
        (fun heq => ?_) (fun hne => ?_))))))
    · simp (disch := decide) only [upd_same, upd_other] at heq
      rw [h.a3, h.a6, strlenWordVal_eq] at heq
      have h16 := htest.1 heq
      refine ih (t + 8) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h16, ?_, hp⟩
      all_goals try simp (disch := decide) only [upd_same, upd_other]
      · exact h.ra
      · exact h.a0
      · rw [h.a1]; exact a4_plus8 s t
      · rw [h.a2]; exact a4_plus8 d t
      · exact h.a3
      · exact word_bytes hf h16
      · exact h.a6
      · have := h.al; omega
    · simp (disch := decide) only [upd_same, upd_other] at hne
      rw [h.a3, h.a6, strlenWordVal_eq] at hne
      refine tailCpy c ⟨?_, ?_, ?_, ?_, hle, ?_, hp⟩
      all_goals try simp (disch := decide) only [upd_same, upd_other]
      · exact h.ra
      · exact h.a0
      · rw [h.a1]; exact a4_plus8 s t
      · rw [h.a2]; exact a4_plus8 d t
      · exact Classical.byContradiction fun hc => hne (htest.2 (by omega))

/-- **`strcpy` from its entry.** -/
theorem strcpyRun (c : CCtx live d s r len bv N) {R : Nat → BitVec 64} {Mt : Mem}
    (h1 : R 1 = r) (h10 : R 10 = d) (h11 : R 11 = s) : CW live d s r len bv N 0x80006dc4#64 R Mt := by
  have hroom := c.room; have hdhi := c.dhi; have hnw := c.src.regions.nowrap
  refine sl_80006dc4 c.src.code (sl_80006dc8 c.src.code (sl_80006dcc c.src.code
    (fun hnz => ?_) (fun hz => ?_)))
  · -- misaligned: the byte loop
    refine sl_80006e7c c.src.code (byteRun c len 0 _ Mt (by omega) ⟨?_, ?_, ?_, ?_, Nat.zero_le _,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    all_goals try simp (disch := decide) only [upd_same, upd_other]
    · exact h1
    · exact h10
    · rw [h11]; exact (BitVec.add_zero s).symm
    · rw [h10, sext0_add]; exact (BitVec.add_zero d).symm
  · simp (disch := decide) only [upd_same, upd_other, Classical.not_not] at hz
    rw [h10, h11] at hz
    have hal := or_aligned hz
    refine sl_80006dd0 c.src.code (sl_80006dd4 c.src.code (slH_80006dd8 c.src.code ?_ fun f hf => ?_))
    · simp (disch := decide) only [upd_same, upd_other]; rw [h11, sext0_add]
      exact ldok c.src (k := 0) (by omega)
    simp (disch := decide) only [upd_same, upd_other]
    rw [h11, sext0_add]
    have htest := word_test c.src hf (t := 0) (Nat.zero_le _)
    rw [Nat.add_zero] at htest
    refine sl_80006ddc c.src.code (sl_80006de0 c.src.code (sl_80006de4 c.src.code
      (sl_80006de8 c.src.code (sl_80006dec c.src.code (sl_80006df0 c.src.code
        (sl_80006df4 c.src.code (sl_80006df8 c.src.code (sl_80006dfc c.src.code
          (fun hne => ?_) (fun heq => ?_)))))))))
    · simp (disch := decide) only [upd_same, upd_other] at hne
      rw [magic_build, allOnes_build, strlenWordVal_eq] at hne
      refine tailCpy c ⟨?_, ?_, ?_, ?_, Nat.zero_le _, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      all_goals try simp (disch := decide) only [upd_same, upd_other]
      · exact h1
      · exact h10
      · rw [h11]; exact (BitVec.add_zero s).symm
      · rw [h10, sext0_add]; exact (BitVec.add_zero d).symm
      · exact Classical.byContradiction fun hc => hne (htest.2 (by omega))
    · simp (disch := decide) only [upd_same, upd_other, Classical.not_not] at heq
      rw [magic_build, allOnes_build, strlenWordVal_eq] at heq
      have h8 := htest.1 heq
      refine wordCpy c len 0 _ Mt (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      all_goals try simp (disch := decide) only [upd_same, upd_other]
      · exact h1
      · exact h10
      · rw [h11]; exact (BitVec.add_zero s).symm
      · rw [h10, sext0_add]; exact (BitVec.add_zero d).symm
      · exact magic_build
      · intro i hi; rw [show s.toNat = s.toNat + 0 from rfl]; exact word_bytes hf h8 i hi
      · rw [magic_build, strlenWordVal_eq]; exact heq

end VsaIris.Interp.StrLeaf

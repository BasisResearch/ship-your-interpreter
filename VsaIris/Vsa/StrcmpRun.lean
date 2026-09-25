import VsaIris.Vsa.StrcmpRunBase

/-!
# `strcmp` as one bounded run

The byte loop, the lane compare, the NUL-word exits and the aligned word loop,
each a lemma over `CRun` (`StrcmpRunBase.lean`), composed into `strcmpRun`.
-/

namespace VsaIris.Inst.Strcmp

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim Vsa.MemRepr
open VsaIris.Inst.Strlen (codeText)

section Run

variable {live : Nat → Prop} {p q r : BitVec 64} {cx cy : List Char} {ix iy : Nat → BitVec 8}

/-! ## Byte facts -/

theorem SBytes.lt128 {img : Nat → BitVec 8} {a : Nat} {cs : List Char} (h : SBytes img a cs)
    {k : Nat} (hk : k ≤ cs.length) : byteVal cs k < 128 := by
  rcases Nat.lt_or_ge k cs.length with h1 | h1
  · exact (h.ascii k h1).2
  · have : k = cs.length := by omega
    subst this
    unfold byteVal; simp

theorem SBytes.zero_iff {img : Nat → BitVec 8} {a : Nat} {cs : List Char} (h : SBytes img a cs)
    {k : Nat} (hk : k ≤ cs.length) : byteVal cs k = 0 ↔ k = cs.length := by
  constructor
  · intro h0
    rcases Nat.lt_or_ge k cs.length with h1 | h1
    · have := (h.ascii k h1).1; omega
    · omega
  · intro e; subst e; unfold byteVal; simp

theorem SWin.ptr {a len : Nat} (h : SWin a len) (P : BitVec 64) (hP : P.toNat = a) {k : Nat}
    (hk : k ≤ len + 8) : (P + BitVec.ofNat 64 k).toNat = a + k := by
  have := h.hi
  rw [ptrN P k (by omega), hP]

theorem SWin.ld {a len : Nat} (h : SWin a len) {k w : Nat} (hk : k + w ≤ len + 8) :
    0x80000000 ≤ a + k ∧ a + k + w ≤ 0x100000000 ∧
      (a + k + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ a + k) := by
  have h1 := h.lo; have h2 := h.hi; have h3 := h.htif
  refine ⟨by omega, by omega, ?_⟩
  rcases h3 with h3 | h3
  · left; omega
  · right; omega

theorem zext_toNat8 (b : BitVec 8) : (zero_extend (m := 64) b).toNat = b.toNat := zext_toNat b

theorem zext_eq_iff (a b : BitVec 8) :
    zero_extend (m := 64) a = zero_extend (m := 64) b ↔ a.toNat = b.toNat := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; rwa [zext_toNat, zext_toNat] at this
  · intro h; apply BitVec.eq_of_toNat_eq; rw [zext_toNat, zext_toNat, h]

theorem strcmpSign_self (v : BitVec 64) : strcmpSign (v - v) = 0 := by
  simp [strcmpSign]

/-! ## The return `sub a0,a2,a3; ret` (`0x80006f9c`) -/

theorem ret_f9c (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64}
    (hpc : rv VsaIris.PC = 0x80006f9c#64) (hra : rv 1 = r)
    (hs : strcmpSign (rv 12 - rv 13) = strcmpSpecSign cx cy) :
    CRun live (TT p q cx cy ix iy) r cx cy 1 rv := by
  refine cmpStep 0 ctx.codeL codeT strcmpX6f9cSeg [] (fun _ => []) _ _ rfl (by decide)
    (by decide) (fun _ => rfl) hpc ?_ ?_
  · intro vals _ m hl _
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    change (Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [hra, ret_tgt r ctx.ret]; exact ctx.ret
  · intro vals _ rv' hpc' hfin
    refine CRun.done ⟨?_, ?_, ?_⟩
    · rw [hpc']
      show Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1 = r
      rw [hra, ret_tgt r ctx.ret]
    · rw [hfin 1 (by decide)]; exact hra
    · rw [hfin 10 (by decide)]; exact hs

/-! ## The byte loop (`0x80006f84 … 0x80006fa0`) -/

/-- One iteration of the byte loop: return, or the head at `k + 1`. -/
theorem byteStep (ctx : Ctx live p q r cx cy ix iy) {k : Nat} {rv : Nat → BitVec 64}
    (h : ByteSt p q r cx cy k rv) (m : Nat)
    (hk : ∀ rv', ByteSt p q r cx cy (k + 1) rv' → CRun live (TT p q cx cy ix iy) r cx cy m rv') :
    CRun live (TT p q cx cy ix iy) r cx cy (m + 3) rv := by
  have hkx : k ≤ cx.length := prefix_le_lena h.pre
  have hky : k ≤ cy.length := prefix_le_lenb h.pre
  have hax : (rv 10).toNat = p.toNat + k := by
    rw [h.a0]; exact ctx.wx.ptr p rfl (by omega)
  have hay : (rv 11).toNat = q.toNat + k := by
    rw [h.a1]; exact ctx.wy.ptr q rfl (by omega)
  have hlx := ctx.wx.ld (k := k) (w := 1) (by omega)
  have hly := ctx.wy.ld (k := k) (w := 1) (by omega)
  -- the two bytes, as the machine holds them
  have hbx : ∀ vals : Nat → BitVec 8, (∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2) →
      (vals (p.toNat + k)).toNat = byteVal cx k := fun vals hv => by
    rw [valsX hv k hkx]; exact ctx.bx.byte k hkx
  have hby : ∀ vals : Nat → BitVec 8, (∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2) →
      (vals (q.toNat + k)).toNat = byteVal cy k := fun vals hv => by
    rw [valsY hv k hky]; exact ctx.by_.byte k hky
  have hmem : ∀ (vals : Nat → BitVec 8) (m : Std.ExtHashMap Nat (BitVec 8)),
      (∀ a ∈ [p.toNat + k, q.toNat + k], (m[a]?).getD 0 = vals a) →
      (m[p.toNat + k]?).getD 0 = vals (p.toNat + k) ∧ (m[q.toNat + k]?).getD 0 = vals (q.toNat + k) :=
    fun _ _ hpk => ⟨hpk _ (by simp), hpk _ (by simp)⟩
  by_cases hne : byteVal cx k = byteVal cy k
  · -- equal bytes: `bne a2,a3` falls through to `bnez a2`
    refine cmpStep (m + 2) ctx.codeL codeT strcmpX6f84FSeg [p.toNat + k, q.toNat + k]
      (fun vals => [[vals (p.toNat + k)], [vals (q.toNat + k)]]) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals hv m hl hpk
      obtain ⟨h1, h2⟩ := hmem vals m hpk
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      · refine lbuF rfl ?_ hlx.1 hlx.2.1 hlx.2.2 h1
        show (rv 10 + sign_extend (m := 64) (0x000#12)).toNat = _
        rw [sext0_add, hax]
      · refine lbuF rfl ?_ hly.1 hly.2.1 hly.2.2 h2
        show (rv 11 + sign_extend (m := 64) (0x000#12)).toNat = _
        rw [sext0_add, hay]
      · change (zero_extend (m := 64) (vals (p.toNat + k)) !=
          zero_extend (m := 64) (vals (q.toNat + k))) = false
        rw [bne_eq_false_iff_eq, zext_eq_iff, hbx vals hv, hby vals hv, hne]
    · intro vals hv rv1 hpc1 hfin1
      have e12 : rv1 12 = zero_extend (m := 64) (vals (p.toNat + k)) := hfin1 12 (by decide)
      have e13 : rv1 13 = zero_extend (m := 64) (vals (q.toNat + k)) := hfin1 13 (by decide)
      have e10 : rv1 10 = rv 10 + sign_extend (m := 64) (0x001#12) := hfin1 10 (by decide)
      have e11 : rv1 11 = rv 11 + sign_extend (m := 64) (0x001#12) := hfin1 11 (by decide)
      have e1 : rv1 1 = rv 1 := hfin1 1 (by decide)
      have hx := hbx vals hv
      have hy := hby vals hv
      have hpc1' : rv1 VsaIris.PC = 0x80006f98#64 := hpc1
      by_cases hz : byteVal cx k = 0
      · -- both NUL: `bnez a2` falls through to the return, `a0 = 0`
        refine CRun.mono (by omega : 2 ≤ m + 2) ?_
        refine cmpStep 1 ctx.codeL codeT strcmpX6f98FSeg [] (fun _ => []) _ _ rfl (by decide)
          (by decide) (fun _ => rfl) hpc1' ?_ ?_
        · intro vals' _ m' hl _
          chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
          change (rv1 12 != 0#64) = false
          rw [bne_eq_false_iff_eq, e12]
          apply BitVec.eq_of_toNat_eq
          rw [zext_toNat, hx, hz]; rfl
        · intro vals' _ rv2 hpc2 hfin2
          refine ret_f9c ctx hpc2 ((hfin2 1 (by decide)).trans (e1.trans h.ra)) ?_
          rw [hfin2 12 (by decide), hfin2 13 (by decide)]
          show strcmpSign (rv1 12 - rv1 13) = _
          have hzq : zero_extend (m := 64) (vals (q.toNat + k)) =
              zero_extend (m := 64) (vals (p.toNat + k)) := (zext_eq_iff _ _).2 (by rw [hx, hy, hne])
          rw [e12, e13, hzq]
          rw [strcmpSign_self, strcmpSpecSign_eq cx cy k h.pre
            ((ctx.bx.zero_iff hkx).1 hz).symm ((ctx.by_.zero_iff hky).1 (hne ▸ hz)).symm]
      · -- a nonzero equal byte: the head at `k + 1`
        refine cmpStep (m + 1) ctx.codeL codeT strcmpX6f98TSeg [] (fun _ => []) _ _ rfl (by decide)
          (by decide) (fun _ => rfl) hpc1' ?_ ?_
        · intro vals' _ m' hl _
          chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
          change (rv1 12 != 0#64) = true
          rw [bne_iff_ne, ne_eq, e12]
          intro h0
          have := congrArg BitVec.toNat h0
          rw [zext_toNat, hx] at this
          exact hz this
        · intro vals' _ rv2 hpc2 hfin2
          refine CRun.mono (by omega) (hk rv2 ⟨hpc2, (hfin2 1 (by decide)).trans (e1.trans h.ra), ?_, ?_, ?_⟩)
          · rw [hfin2 10 (by decide)]; show rv1 10 = _; rw [e10, h.a0, ptr_incr1]
          · rw [hfin2 11 (by decide)]; show rv1 11 = _; rw [e11, h.a1, ptr_incr1]
          · intro i hi
            rcases Nat.lt_or_ge i k with hik | hik
            · exact h.pre i hik
            · have : i = k := by omega
              subst this; exact ⟨hne, hz⟩
  · -- differing bytes: `bne a2,a3` to the return
    refine CRun.mono (by omega : 2 ≤ m + 3) ?_
    refine cmpStep 1 ctx.codeL codeT strcmpX6f84TSeg [p.toNat + k, q.toNat + k]
      (fun vals => [[vals (p.toNat + k)], [vals (q.toNat + k)]]) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals hv m hl hpk
      obtain ⟨h1, h2⟩ := hmem vals m hpk
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      · refine lbuF rfl ?_ hlx.1 hlx.2.1 hlx.2.2 h1
        show (rv 10 + sign_extend (m := 64) (0x000#12)).toNat = _
        rw [sext0_add, hax]
      · refine lbuF rfl ?_ hly.1 hly.2.1 hly.2.2 h2
        show (rv 11 + sign_extend (m := 64) (0x000#12)).toNat = _
        rw [sext0_add, hay]
      · change (zero_extend (m := 64) (vals (p.toNat + k)) !=
          zero_extend (m := 64) (vals (q.toNat + k))) = true
        rw [bne_iff_ne, ne_eq, zext_eq_iff, hbx vals hv, hby vals hv]
        exact hne
    · intro vals hv rv1 hpc1 hfin1
      refine ret_f9c ctx hpc1 ((hfin1 1 (by decide)).trans h.ra) ?_
      rw [hfin1 12 (by decide), hfin1 13 (by decide)]
      show strcmpSign (zero_extend (m := 64) (vals (p.toNat + k)) -
        zero_extend (m := 64) (vals (q.toNat + k))) = _
      have hx := hbx vals hv
      have hy := hby vals hv
      rw [strcmpSign_sub _ _ (by rw [hx]; exact ctx.bx.lt128 hkx) (by rw [hy]; exact ctx.by_.lt128 hky),
        hx, hy, strcmpSpecSign_at cx cy k h.pre hne]

theorem byteLoop (ctx : Ctx live p q r cx cy ix iy) :
    ∀ (n k : Nat) (rv : Nat → BitVec 64), cx.length - k = n → ByteSt p q r cx cy k rv →
      CRun live (TT p q cx cy ix iy) r cx cy (3 * n + 3) rv := by
  intro n
  induction n with
  | zero =>
    intro k rv hn h
    refine byteStep ctx h 0 fun rv' h' => ?_
    have := prefix_le_lena h'.pre; omega
  | succ n ih =>
    intro k rv hn h
    have := byteStep ctx h (3 * n + 3) fun rv' h' => ih (k + 1) rv' (by omega) h'
    exact CRun.mono (by omega) this

/-! ## The lane compare (`0x80006f20 … 0x80006f80`)

The words `A` (of `x`) and `B` (of `y`) differ; `d` is their first differing
byte, and its sign decides the result (`LaneDiff`). The three `slli` probes
find the 16-bit lane holding `d`; `srli 0x30` extracts it, and either the
low bytes differ (`zext.b` both, subtract) or the lane difference is `256`
times the high bytes' difference. -/

/-- Byte `i` of a word. -/
abbrev wb (w : BitVec 64) (i : Nat) : BitVec 8 := w.extractLsb' (8 * i) 8

/-- The words' first differing byte `d`, below 128 on both sides, has sign `sg`. -/
structure LaneDiff (A B : BitVec 64) (sg : Int) (d : Nat) : Prop where
  lt : d < 8
  pre : ∀ i, i < d → wb A i = wb B i
  ne : wb A d ≠ wb B d
  ha : (wb A d).toNat < 128
  hb : (wb B d).toNat < 128
  sign : isign (wb A d).toNat (wb B d).toNat = sg

theorem LaneDiff.agree_iff {A B : BitVec 64} {sg : Int} {d : Nat} (h : LaneDiff A B sg d)
    (n : Nat) : (∀ m, m < n → wb A m = wb B m) ↔ n ≤ d := by
  constructor
  · intro hall
    rcases Nat.lt_or_ge d n with h1 | h1
    · exact absurd (hall d h1) h.ne
    · exact h1
  · intro hnd m hm; exact h.pre m (by omega)

theorem zext_ne_zero (b : BitVec 8) : zero_extend (m := 64) b ≠ 0#64 ↔ b ≠ 0#8 := by
  constructor
  · intro h h0; apply h; rw [h0]; rfl
  · intro h h0; apply h
    have := congrArg BitVec.toNat h0
    rw [zext_toNat] at this
    exact BitVec.eq_of_toNat_eq this

/-- The `zext.b` guard of a lane difference: nonzero iff the low bytes differ. -/
theorem lane_guard (X Y : BitVec 64) (hX : X.toNat < 2 ^ 16) (hY : Y.toNat < 2 ^ 16) :
    ((X - Y) &&& sign_extend (m := 64) (0x0ff#12)) ≠ 0#64 ↔
      X.extractLsb' 0 8 ≠ Y.extractLsb' 0 8 := by
  rw [andi_ff_eq_zext_byte, zext_ne_zero, ne_eq, ne_eq, block_diff_lo_zero X Y hX hY]

/-- The first difference in the lane's low byte: `zext.b` both and subtract. -/
theorem lane_sign_lo {A B : BitVec 64} {sg : Int} {s : Nat} (hs : s ≤ 6)
    (h : LaneDiff A B sg (6 - s)) :
    strcmpSign (zero_extend (m := 64) (((A <<< (8 * s)) >>> (48 : Nat)).extractLsb' 0 8) -
      zero_extend (m := 64) (((B <<< (8 * s)) >>> (48 : Nat)).extractLsb' 0 8)) = sg := by
  rw [shl_shr48_lo A s hs, shl_shr48_lo B s hs, strcmpSign_sub _ _ h.ha h.hb]
  exact h.sign

/-- The first difference in the lane's high byte: the lane difference. -/
theorem lane_sign_hi {A B : BitVec 64} {sg : Int} {s : Nat} (hs : s ≤ 6)
    (h : LaneDiff A B sg (7 - s)) :
    strcmpSign (((A <<< (8 * s)) >>> (48 : Nat)) - ((B <<< (8 * s)) >>> (48 : Nat))) = sg := by
  have hX := shr48_lt (A <<< (8 * s))
  have hY := shr48_lt (B <<< (8 * s))
  have hlo : wb A (6 - s) = wb B (6 - s) := h.pre (6 - s) (by omega)
  have hlo' : (A.extractLsb' (8 * (6 - s)) 8).toNat = (B.extractLsb' (8 * (6 - s)) 8).toNat :=
    congrArg BitVec.toNat hlo
  rw [← shl_shr48_lo A s hs, ← shl_shr48_lo B s hs, block_lo, block_lo] at hlo'
  have hhA : (((A <<< (8 * s)) >>> (48 : Nat)).extractLsb' 8 8).toNat = (wb A (7 - s)).toNat := by
    rw [shl_shr48_hi A s hs]
  have hhB : (((B <<< (8 * s)) >>> (48 : Nat)).extractLsb' 8 8).toNat = (wb B (7 - s)).toNat := by
    rw [shl_shr48_hi B s hs]
  rw [block_hi _ hX] at hhA
  rw [block_hi _ hY] at hhB
  rw [strcmpSign_block_sub _ _ hX hY hlo' (by rw [hhA]; exact h.ha) (by rw [hhB]; exact h.hb),
    hhA, hhB]
  exact h.sign

theorem lane_guard_iff {A B : BitVec 64} {sg : Int} {s d : Nat} (hs : s ≤ 6)
    (h : LaneDiff A B sg d) (hdl : 6 - s ≤ d) :
    ((((A <<< (8 * s)) >>> (48 : Nat)) - ((B <<< (8 * s)) >>> (48 : Nat))) &&&
      sign_extend (m := 64) (0x0ff#12)) ≠ 0#64 ↔ d = 6 - s := by
  rw [lane_guard _ _ (shr48_lt _) (shr48_lt _), shl_shr48_lo A s hs, shl_shr48_lo B s hs]
  constructor
  · intro hne
    rcases Nat.lt_or_ge (6 - s) d with h1 | h1
    · exact absurd (h.pre _ h1) hne
    · omega
  · intro e; subst e; exact h.ne

/-- A bare `ret` with the result already in `a0` (`0x80006f58`). -/
theorem ret_f58 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64}
    (hpc : rv VsaIris.PC = 0x80006f58#64) (hra : rv 1 = r)
    (hs : strcmpSign (rv 10) = strcmpSpecSign cx cy) :
    CRun live (TT p q cx cy ix iy) r cx cy 1 rv := by
  refine cmpStep 0 ctx.codeL codeT strcmpX6f58Seg [] (fun _ => []) _ _ rfl (by decide)
    (by decide) (fun _ => rfl) hpc ?_ ?_
  · intro vals _ m hl _
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    change (Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [hra, ret_tgt r ctx.ret]; exact ctx.ret
  · intro vals _ rv' hpc' hfin
    refine CRun.done ⟨?_, ?_, ?_⟩
    · rw [hpc']
      show Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1 = r
      rw [hra, ret_tgt r ctx.ret]
    · rw [hfin 1 (by decide)]; exact hra
    · rw [hfin 10 (by decide)]; exact hs

/-- A bare `ret` with the result already in `a0` (`0x80006f70`). -/
theorem ret_f70 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64}
    (hpc : rv VsaIris.PC = 0x80006f70#64) (hra : rv 1 = r)
    (hs : strcmpSign (rv 10) = strcmpSpecSign cx cy) :
    CRun live (TT p q cx cy ix iy) r cx cy 1 rv := by
  refine cmpStep 0 ctx.codeL codeT strcmpX6f70Seg [] (fun _ => []) _ _ rfl (by decide)
    (by decide) (fun _ => rfl) hpc ?_ ?_
  · intro vals _ m hl _
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    change (Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [hra, ret_tgt r ctx.ret]; exact ctx.ret
  · intro vals _ rv' hpc' hfin
    refine CRun.done ⟨?_, ?_, ?_⟩
    · rw [hpc']
      show Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1 = r
      rw [hra, ret_tgt r ctx.ret]
    · rw [hfin 1 (by decide)]; exact hra
    · rw [hfin 10 (by decide)]; exact hs

/-- `zext.b a4; zext.b a5; sub a0,a4,a5; ret` (`0x80006f74`). -/
theorem ret_f74 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64}
    (hpc : rv VsaIris.PC = 0x80006f74#64) (hra : rv 1 = r)
    (hs : strcmpSign (zero_extend (m := 64) ((rv 14).extractLsb' 0 8) -
      zero_extend (m := 64) ((rv 15).extractLsb' 0 8)) = strcmpSpecSign cx cy) :
    CRun live (TT p q cx cy ix iy) r cx cy 1 rv := by
  refine cmpStep 0 ctx.codeL codeT strcmpX6f74Seg [] (fun _ => []) _ _ rfl (by decide)
    (by decide) (fun _ => rfl) hpc ?_ ?_
  · intro vals _ m hl _
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    change (Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [hra, ret_tgt r ctx.ret]; exact ctx.ret
  · intro vals _ rv' hpc' hfin
    refine CRun.done ⟨?_, ?_, ?_⟩
    · rw [hpc']
      show Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1 = r
      rw [hra, ret_tgt r ctx.ret]
    · rw [hfin 1 (by decide)]; exact hra
    · rw [hfin 10 (by decide)]
      show strcmpSign ((rv 14 &&& sign_extend (m := 64) (0x0ff#12)) -
        (rv 15 &&& sign_extend (m := 64) (0x0ff#12))) = _
      rw [andi_ff_eq_zext_byte, andi_ff_eq_zext_byte]; exact hs

/-- The lane at `0x80006f5c`: `a4 = A <<< 8s`, `a5 = B <<< 8s`, the first
difference in bytes `6-s` or `7-s`. -/
theorem laneF5c (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64} {A B : BitVec 64}
    {d s : Nat} (hs : s ≤ 6) (hpc : rv VsaIris.PC = 0x80006f5c#64) (hra : rv 1 = r)
    (h14 : rv 14 = A <<< (8 * s)) (h15 : rv 15 = B <<< (8 * s))
    (hd : LaneDiff A B (strcmpSpecSign cx cy) d) (hdl : 6 - s ≤ d) (hdh : d ≤ 7 - s) :
    CRun live (TT p q cx cy ix iy) r cx cy 3 rv := by
  have hg := lane_guard_iff hs hd hdl
  have e14 : shift_bits_right (rv 14) (Sail.BitVec.extractLsb (0x30#6) 5 0) =
      (A <<< (8 * s)) >>> (48 : Nat) := by rw [shr_48, h14]
  have e15 : shift_bits_right (rv 15) (Sail.BitVec.extractLsb (0x30#6) 5 0) =
      (B <<< (8 * s)) >>> (48 : Nat) := by rw [shr_48, h15]
  by_cases hlo : d = 6 - s
  · refine CRun.mono (by omega : 2 ≤ 3) ?_
    refine cmpStep 1 ctx.codeL codeT strcmpX6f5cTSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change ((((shift_bits_right (rv 14) (Sail.BitVec.extractLsb (0x30#6) 5 0)) -
        (shift_bits_right (rv 15) (Sail.BitVec.extractLsb (0x30#6) 5 0))) &&&
          sign_extend (m := 64) (0x0ff#12)) != 0#64) = true
      rw [e14, e15, bne_iff_ne]; exact hg.2 hlo
    · intro vals _ rv' hpc' hfin
      refine ret_f74 ctx hpc' ((hfin 1 (by decide)).trans hra) ?_
      rw [hfin 14 (by decide), hfin 15 (by decide)]
      show strcmpSign (zero_extend (m := 64)
        ((shift_bits_right (rv 14) (Sail.BitVec.extractLsb (0x30#6) 5 0)).extractLsb' 0 8) -
        zero_extend (m := 64)
        ((shift_bits_right (rv 15) (Sail.BitVec.extractLsb (0x30#6) 5 0)).extractLsb' 0 8)) = _
      rw [e14, e15]
      exact lane_sign_lo hs (hlo ▸ hd)
  · refine CRun.mono (by omega : 2 ≤ 3) ?_
    refine cmpStep 1 ctx.codeL codeT strcmpX6f5cFSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change ((((shift_bits_right (rv 14) (Sail.BitVec.extractLsb (0x30#6) 5 0)) -
        (shift_bits_right (rv 15) (Sail.BitVec.extractLsb (0x30#6) 5 0))) &&&
          sign_extend (m := 64) (0x0ff#12)) != 0#64) = false
      rw [e14, e15, bne_eq_false_iff_eq]
      exact Decidable.byContradiction fun hc => hlo (hg.1 hc)
    · intro vals _ rv' hpc' hfin
      refine ret_f70 ctx hpc' ((hfin 1 (by decide)).trans hra) ?_
      rw [hfin 10 (by decide)]
      show strcmpSign ((shift_bits_right (rv 14) (Sail.BitVec.extractLsb (0x30#6) 5 0)) -
        (shift_bits_right (rv 15) (Sail.BitVec.extractLsb (0x30#6) 5 0))) = _
      rw [e14, e15]
      exact lane_sign_hi hs (show 7 - s = d by omega ▸ hd)

/-- The last lane at `0x80006f44`: bytes 6 and 7, read from `a2`/`a3`. -/
theorem laneF44 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64} {A B : BitVec 64}
    {d : Nat} (hpc : rv VsaIris.PC = 0x80006f44#64) (hra : rv 1 = r)
    (h12 : rv 12 = A) (h13 : rv 13 = B)
    (hd : LaneDiff A B (strcmpSpecSign cx cy) d) (hdl : 6 ≤ d) :
    CRun live (TT p q cx cy ix iy) r cx cy 3 rv := by
  have hA0 : A = A <<< (8 * 0) := by simp
  have hB0 : B = B <<< (8 * 0) := by simp
  have hg := lane_guard_iff (s := 0) (by omega) hd hdl
  have e14 : shift_bits_right (rv 12) (Sail.BitVec.extractLsb (0x30#6) 5 0) =
      (A <<< (8 * 0)) >>> (48 : Nat) := by rw [shr_48, h12, ← hA0]
  have e15 : shift_bits_right (rv 13) (Sail.BitVec.extractLsb (0x30#6) 5 0) =
      (B <<< (8 * 0)) >>> (48 : Nat) := by rw [shr_48, h13, ← hB0]
  by_cases hlo : d = 6 - 0
  · refine CRun.mono (by omega : 2 ≤ 3) ?_
    refine cmpStep 1 ctx.codeL codeT strcmpX6f44TSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change ((((shift_bits_right (rv 12) (Sail.BitVec.extractLsb (0x30#6) 5 0)) -
        (shift_bits_right (rv 13) (Sail.BitVec.extractLsb (0x30#6) 5 0))) &&&
          sign_extend (m := 64) (0x0ff#12)) != 0#64) = true
      rw [e14, e15, bne_iff_ne]; exact hg.2 hlo
    · intro vals _ rv' hpc' hfin
      refine ret_f74 ctx hpc' ((hfin 1 (by decide)).trans hra) ?_
      rw [hfin 14 (by decide), hfin 15 (by decide)]
      show strcmpSign (zero_extend (m := 64)
        ((shift_bits_right (rv 12) (Sail.BitVec.extractLsb (0x30#6) 5 0)).extractLsb' 0 8) -
        zero_extend (m := 64)
        ((shift_bits_right (rv 13) (Sail.BitVec.extractLsb (0x30#6) 5 0)).extractLsb' 0 8)) = _
      rw [e14, e15]
      exact lane_sign_lo (by omega) (hlo ▸ hd)
  · refine CRun.mono (by omega : 2 ≤ 3) ?_
    refine cmpStep 1 ctx.codeL codeT strcmpX6f44FSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change ((((shift_bits_right (rv 12) (Sail.BitVec.extractLsb (0x30#6) 5 0)) -
        (shift_bits_right (rv 13) (Sail.BitVec.extractLsb (0x30#6) 5 0))) &&&
          sign_extend (m := 64) (0x0ff#12)) != 0#64) = false
      rw [e14, e15, bne_eq_false_iff_eq]
      exact Decidable.byContradiction fun hc => hlo (hg.1 hc)
    · intro vals _ rv' hpc' hfin
      refine ret_f58 ctx hpc' ((hfin 1 (by decide)).trans hra) ?_
      rw [hfin 10 (by decide)]
      show strcmpSign ((shift_bits_right (rv 12) (Sail.BitVec.extractLsb (0x30#6) 5 0)) -
        (shift_bits_right (rv 13) (Sail.BitVec.extractLsb (0x30#6) 5 0))) = _
      rw [e14, e15]
      exact lane_sign_hi (by omega) (show 7 - 0 = d by have := hd.lt; omega ▸ hd)

/-- The third probe (`slli 0x10`, `0x80006f38`): bytes `0 … 5`. -/
theorem laneF38 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64} {A B : BitVec 64}
    {d : Nat} (hpc : rv VsaIris.PC = 0x80006f38#64) (hra : rv 1 = r)
    (h12 : rv 12 = A) (h13 : rv 13 = B)
    (hd : LaneDiff A B (strcmpSpecSign cx cy) d) (hdl : 4 ≤ d) :
    CRun live (TT p q cx cy ix iy) r cx cy 4 rv := by
  have e14 : shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x10#6) 5 0) = A <<< (8 * 2) := by
    rw [shl_16, h12]
  have e15 : shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x10#6) 5 0) = B <<< (8 * 2) := by
    rw [shl_16, h13]
  have hg : A <<< (8 * 2) = B <<< (8 * 2) ↔ 6 ≤ d := (slli16_eq_iff A B).trans (hd.agree_iff 6)
  by_cases hlt : d < 6
  · refine CRun.mono (by omega : 4 ≤ 4) ?_
    refine cmpStep 3 ctx.codeL codeT strcmpX6f38TSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x10#6) 5 0) !=
        shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x10#6) 5 0)) = true
      rw [e14, e15, bne_iff_ne]; exact fun he => by have := hg.1 he; omega
    · intro vals _ rv' hpc' hfin
      exact laneF5c ctx (s := 2) (by omega) hpc' ((hfin 1 (by decide)).trans hra)
        ((hfin 14 (by decide)).trans e14) ((hfin 15 (by decide)).trans e15) hd (by omega)
        (by omega)
  · refine cmpStep 3 ctx.codeL codeT strcmpX6f38FSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x10#6) 5 0) !=
        shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x10#6) 5 0)) = false
      rw [e14, e15, bne_eq_false_iff_eq]; exact hg.2 (by omega)
    · intro vals _ rv' hpc' hfin
      exact laneF44 ctx hpc' ((hfin 1 (by decide)).trans hra)
        ((hfin 12 (by decide)).trans h12) ((hfin 13 (by decide)).trans h13) hd (by omega)

/-- The second probe (`slli 0x20`, `0x80006f2c`): bytes `0 … 3`. -/
theorem laneF2c (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64} {A B : BitVec 64}
    {d : Nat} (hpc : rv VsaIris.PC = 0x80006f2c#64) (hra : rv 1 = r)
    (h12 : rv 12 = A) (h13 : rv 13 = B)
    (hd : LaneDiff A B (strcmpSpecSign cx cy) d) (hdl : 2 ≤ d) :
    CRun live (TT p q cx cy ix iy) r cx cy 5 rv := by
  have e14 : shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x20#6) 5 0) = A <<< (8 * 4) := by
    rw [shl_32, h12]
  have e15 : shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x20#6) 5 0) = B <<< (8 * 4) := by
    rw [shl_32, h13]
  have hg : A <<< (8 * 4) = B <<< (8 * 4) ↔ 4 ≤ d := (slli32_eq_iff A B).trans (hd.agree_iff 4)
  by_cases hlt : d < 4
  · refine CRun.mono (by omega : 4 ≤ 5) ?_
    refine cmpStep 3 ctx.codeL codeT strcmpX6f2cTSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x20#6) 5 0) !=
        shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x20#6) 5 0)) = true
      rw [e14, e15, bne_iff_ne]; exact fun he => by have := hg.1 he; omega
    · intro vals _ rv' hpc' hfin
      exact laneF5c ctx (s := 4) (by omega) hpc' ((hfin 1 (by decide)).trans hra)
        ((hfin 14 (by decide)).trans e14) ((hfin 15 (by decide)).trans e15) hd (by omega)
        (by omega)
  · refine cmpStep 4 ctx.codeL codeT strcmpX6f2cFSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x20#6) 5 0) !=
        shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x20#6) 5 0)) = false
      rw [e14, e15, bne_eq_false_iff_eq]; exact hg.2 (by omega)
    · intro vals _ rv' hpc' hfin
      exact laneF38 ctx hpc' ((hfin 1 (by decide)).trans hra)
        ((hfin 12 (by decide)).trans h12) ((hfin 13 (by decide)).trans h13) hd (by omega)

/-- **The lane compare** from `0x80006f20` (`slli 0x30`: bytes `0, 1`). -/
theorem laneRun (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64} {A B : BitVec 64}
    {d : Nat} (hpc : rv VsaIris.PC = 0x80006f20#64) (hra : rv 1 = r)
    (h12 : rv 12 = A) (h13 : rv 13 = B)
    (hd : LaneDiff A B (strcmpSpecSign cx cy) d) :
    CRun live (TT p q cx cy ix iy) r cx cy 6 rv := by
  have e14 : shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x30#6) 5 0) = A <<< (8 * 6) := by
    rw [shl_48, h12]
  have e15 : shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x30#6) 5 0) = B <<< (8 * 6) := by
    rw [shl_48, h13]
  have hg : A <<< (8 * 6) = B <<< (8 * 6) ↔ 2 ≤ d := (slli48_eq_iff A B).trans (hd.agree_iff 2)
  by_cases hlt : d < 2
  · refine CRun.mono (by omega : 4 ≤ 6) ?_
    refine cmpStep 3 ctx.codeL codeT strcmpX6f20TSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x30#6) 5 0) !=
        shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x30#6) 5 0)) = true
      rw [e14, e15, bne_iff_ne]; exact fun he => by have := hg.1 he; omega
    · intro vals _ rv' hpc' hfin
      exact laneF5c ctx (s := 6) (by omega) hpc' ((hfin 1 (by decide)).trans hra)
        ((hfin 14 (by decide)).trans e14) ((hfin 15 (by decide)).trans e15) hd (by omega)
        (by omega)
  · refine cmpStep 5 ctx.codeL codeT strcmpX6f20FSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (shift_bits_left (rv 12) (Sail.BitVec.extractLsb (0x30#6) 5 0) !=
        shift_bits_left (rv 13) (Sail.BitVec.extractLsb (0x30#6) 5 0)) = false
      rw [e14, e15, bne_eq_false_iff_eq]; exact hg.2 (by omega)
    · intro vals _ rv' hpc' hfin
      exact laneF2c ctx hpc' ((hfin 1 (by decide)).trans hra)
        ((hfin 12 (by decide)).trans h12) ((hfin 13 (by decide)).trans h13) hd (by omega)

end Run

/-! ## A loaded pair of words

The word loop loads `A` from `x` and `B` from `y` at offset `w`. Bytes at or
before each NUL are the strings' (`WordPair`); the bytes past a NUL are
whatever the machine holds. Every fact below depends only on the former. -/

/-- The words at offset `w` of the two strings, after a byte-equal prefix. -/
structure WordPair (cx cy : List Char) (w : Nat) (A B : BitVec 64) : Prop where
  pre : BytePrefix cx cy w
  a : ∀ k, k < 8 → w + k ≤ cx.length → (wb A k).toNat = byteVal cx (w + k)
  b : ∀ k, k < 8 → w + k ≤ cy.length → (wb B k).toNat = byteVal cy (w + k)

/-- The least index below `n` satisfying a decidable predicate. -/
theorem exists_first (P : Nat → Prop) [DecidablePred P] :
    ∀ n, (∃ k, k < n ∧ P k) → ∃ d, d < n ∧ P d ∧ ∀ i, i < d → ¬ P i
  | 0, ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)
  | n + 1, ⟨k, hk, hP⟩ => by
    by_cases h : ∃ k, k < n ∧ P k
    · obtain ⟨d, hd, hPd, hmin⟩ := exists_first P n h
      exact ⟨d, by omega, hPd, hmin⟩
    · have hkn : k = n := by
        rcases Nat.lt_or_ge k n with h1 | h1
        · exact absurd ⟨k, h1, hP⟩ h
        · omega
      subst hkn
      exact ⟨k, by omega, hP, fun i hi hPi => h ⟨i, hi, hPi⟩⟩

theorem byteVal_len (cs : List Char) : byteVal cs cs.length = 0 := by
  unfold byteVal; simp

section Word

variable {ix iy : Nat → BitVec 8} {a b : Nat} {cx cy : List Char} {w : Nat} {A B : BitVec 64}

/-- The word of `x` has a NUL byte exactly when `x` ends inside it. -/
theorem WordPair.nz_iff (hx : SBytes ix a cx) (h : WordPair cx cy w A B) (hw : w ≤ cx.length) :
    (∀ k, k < 8 → wb A k ≠ 0) ↔ w + 8 ≤ cx.length := by
  constructor
  · intro hnz
    rcases Nat.lt_or_ge cx.length (w + 8) with h1 | h1
    · exfalso
      have hk := h.a (cx.length - w) (by omega) (by omega)
      rw [show w + (cx.length - w) = cx.length by omega, byteVal_len] at hk
      exact hnz (cx.length - w) (by omega) (BitVec.eq_of_toNat_eq hk)
    · exact h1
  · intro h8 k hk h0
    have := h.a k hk (by omega)
    rw [h0] at this
    have := (hx.ascii (w + k) (by omega)).1
    simp_all

/-- In a NUL-free word, `y` cannot end before a byte where the words agree. -/
theorem WordPair.y_long (hx : SBytes ix a cx) (h : WordPair cx cy w A B)
    (hw8 : w + 8 ≤ cx.length) {n : Nat} (hn : n ≤ 8)
    (hag : ∀ i, i < n → wb A i = wb B i) : w + n ≤ cy.length := by
  have hwy := prefix_le_lenb h.pre
  rcases Nat.lt_or_ge cy.length (w + n) with h1 | h1
  · exfalso
    have e := congrArg BitVec.toNat (hag (cy.length - w) (by omega))
    rw [h.a _ (by omega) (by omega), h.b _ (by omega) (by omega),
      show w + (cy.length - w) = cy.length by omega, byteVal_len] at e
    have := (hx.ascii cy.length (by omega)).1
    omega
  · exact h1

/-- The prefix extends over bytes where the words agree, below both NULs. -/
theorem WordPair.extend (hx : SBytes ix a cx) (h : WordPair cx cy w A B) {n : Nat} (hn : n ≤ 8)
    (hnx : w + n ≤ cx.length) (hny : w + n ≤ cy.length)
    (hag : ∀ i, i < n → wb A i = wb B i) (hlt : ∀ i, i < n → w + i < cx.length) :
    BytePrefix cx cy (w + n) := by
  intro i hi
  rcases Nat.lt_or_ge i w with h1 | h1
  · exact h.pre i h1
  · have e := congrArg BitVec.toNat (hag (i - w) (by omega))
    rw [h.a _ (by omega) (by omega), h.b _ (by omega) (by omega),
      show w + (i - w) = i by omega] at e
    have := (hx.ascii i (hlt (i - w) (by omega) |> fun h' => by omega)).1
    exact ⟨e, by omega⟩

/-- Equal NUL-free words: the prefix grows by a word. -/
theorem WordPair.eq_next (hx : SBytes ix a cx) (h : WordPair cx cy w A B)
    (hw8 : w + 8 ≤ cx.length) (heq : A = B) : BytePrefix cx cy (w + 8) := by
  have hag : ∀ i, i < 8 → wb A i = wb B i := fun i _ => by rw [heq]
  exact h.extend hx (by omega) hw8 (h.y_long hx hw8 (by omega) hag) hag
    (fun i hi => by omega)

/-- Differing NUL-free words: the first differing byte decides the sign. -/
theorem WordPair.lane (hx : SBytes ix a cx) (hy : SBytes iy b cy) (h : WordPair cx cy w A B)
    (hw8 : w + 8 ≤ cx.length) (hne : A ≠ B) :
    ∃ d, LaneDiff A B (strcmpSpecSign cx cy) d := by
  obtain ⟨d, hd, hPd, hmin⟩ := exists_first (fun k => wb A k ≠ wb B k) 8
    (word_ne_byte A B hne)
  have hag : ∀ i, i < d → wb A i = wb B i := fun i hi =>
    Decidable.byContradiction (hmin i hi)
  have hdy : w + d ≤ cy.length := h.y_long hx hw8 (by omega) hag
  have hpre := h.extend hx (by omega) (by omega) hdy hag (fun i hi => by omega)
  have ea := h.a d hd (by omega)
  have eb := h.b d hd hdy
  have hbne : byteVal cx (w + d) ≠ byteVal cy (w + d) := by
    rw [← ea, ← eb]; exact fun e => hPd (BitVec.eq_of_toNat_eq e)
  refine ⟨d, hd, hag, hPd, ?_, ?_, ?_⟩
  · rw [ea]; exact hx.lt128 (by omega)
  · rw [eb]; exact hy.lt128 hdy
  · rw [ea, eb, strcmpSpecSign_at cx cy (w + d) hpre hbne]

/-- Equal words, `x`'s holding its NUL: the strings are equal. -/
theorem WordPair.nul_eq (hx : SBytes ix a cx) (hy : SBytes iy b cy) (h : WordPair cx cy w A B)
    (hw : w ≤ cx.length) (hlt : cx.length < w + 8) (heq : A = B) :
    strcmpSpecSign cx cy = 0 := by
  have hwy := prefix_le_lenb h.pre
  have hag : ∀ i, i < 8 → wb A i = wb B i := fun i _ => by rw [heq]
  have hlen : cx.length = cy.length := by
    rcases Nat.lt_trichotomy cy.length cx.length with h1 | h1 | h1
    · exfalso
      have e := congrArg BitVec.toNat (hag (cy.length - w) (by omega))
      rw [h.a _ (by omega) (by omega), h.b _ (by omega) (by omega),
        show w + (cy.length - w) = cy.length by omega, byteVal_len] at e
      have := (hx.ascii cy.length h1).1
      omega
    · exact h1.symm
    · exfalso
      have e := congrArg BitVec.toNat (hag (cx.length - w) (by omega))
      rw [h.a _ (by omega) (by omega), h.b _ (by omega) (by omega),
        show w + (cx.length - w) = cx.length by omega, byteVal_len] at e
      have := (hy.ascii cx.length h1).1
      omega
  have hpre := h.extend hx (n := cx.length - w) (by omega) (by omega) (by omega)
    (fun i hi => hag i (by omega)) (fun i hi => by omega)
  rw [show w + (cx.length - w) = cx.length by omega] at hpre
  exact strcmpSpecSign_eq cx cy cx.length hpre rfl hlen.symm

end Word


section Loop

variable {live : Nat → Prop} {p q r : BitVec 64} {cx cy : List Char} {ix iy : Nat → BitVec 8}

/-! ## The word loop (`0x80006eb8 … 0x80006f1c`) -/

/-- The doubleword a `ld` reads at `a`. -/
abbrev wordAt (vals : Nat → BitVec 8) (a : Nat) : BitVec 64 := bytesVal .ld (bytesAt vals a 8)

/-- The load data of a word-loop group at offset `w`. -/
abbrev ldsW (p q : BitVec 64) (w : Nat) (vals : Nat → BitVec 8) : List (List (BitVec 8)) :=
  [bytesAt vals (p.toNat + w) 8, bytesAt vals (q.toNat + w) 8]

/-- The bytes a word-loop group reads. -/
abbrev peekW (p q : BitVec 64) (w : Nat) : List Nat :=
  (List.range 8).map (p.toNat + w + ·) ++ (List.range 8).map (q.toNat + w + ·)

/-- At a word-loop group (`w = 24j + 8g`), before its loads. -/
structure WSt (p q r : BitVec 64) (cx cy : List Char) (j w : Nat) (pc : BitVec 64)
    (rv : Nat → BitVec 64) : Prop where
  pc : rv VsaIris.PC = pc
  ra : rv 1 = r
  a0 : rv 10 = p + BitVec.ofNat 64 (24 * j)
  a1 : rv 11 = q + BitVec.ofNat 64 (24 * j)
  a5 : rv 15 = magic7f
  t2 : rv 7 = -1#64
  pre : BytePrefix cx cy w
  le : w ≤ cx.length

/-- After a group's loads: `a2 = A`, `a3 = B`. -/
structure LSt (p q r : BitVec 64) (cx cy : List Char) (j w : Nat) (pc : BitVec 64)
    (A B : BitVec 64) (rv : Nat → BitVec 64) : Prop where
  pc : rv VsaIris.PC = pc
  ra : rv 1 = r
  a0 : rv 10 = p + BitVec.ofNat 64 (24 * j)
  a1 : rv 11 = q + BitVec.ofNat 64 (24 * j)
  a5 : rv 15 = magic7f
  t2 : rv 7 = -1#64
  a2 : rv 12 = A
  a3 : rv 13 = B
  pair : WordPair cx cy w A B
  le : w ≤ cx.length

theorem mkPair (ctx : Ctx live p q r cx cy ix iy) {vals : Nat → BitVec 8}
    (hv : ∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2) {w : Nat} (hpre : BytePrefix cx cy w) :
    WordPair cx cy w (wordAt vals (p.toNat + w)) (wordAt vals (q.toNat + w)) := by
  refine ⟨hpre, fun k hk hkx => ?_, fun k hk hky => ?_⟩
  · show (BitVec.extractLsb' (8 * k) 8 (bytesVal .ld (bytesAt vals (p.toNat + w) 8))).toNat = _
    rw [ldWord_byte _ _ _ hk, Nat.add_assoc, valsX hv _ hkx]
    exact ctx.bx.byte _ hkx
  · show (BitVec.extractLsb' (8 * k) 8 (bytesVal .ld (bytesAt vals (q.toNat + w) 8))).toNat = _
    rw [ldWord_byte _ _ _ hk, Nat.add_assoc, valsY hv _ hky]
    exact ctx.by_.byte _ hky

/-- The group's `bne t0,t2`: taken exactly when `x` ends inside the word. -/
theorem grp_guard (ctx : Ctx live p q r cx cy ix iy) {w : Nat} {A B a5 t2 : BitVec 64}
    (hp : WordPair cx cy w A B) (hw : w ≤ cx.length) (h5 : a5 = magic7f) (h7 : t2 = -1#64) :
    ((((A &&& a5) + a5) ||| (A ||| a5)) != t2) = decide (cx.length < w + 8) := by
  rw [h5, h7, strcmpWordVal_eq, neg_one_allOnes]
  have := hp.nz_iff ctx.bx hw
  rw [← detect_all_ones] at this
  by_cases h : cx.length < w + 8
  · rw [decide_eq_true h, bne_iff_ne, ne_eq, this]; omega
  · rw [decide_eq_false h, bne_eq_false_iff_eq, this]; omega

/-- The `ld` address of a group. -/
theorem grp_addr (ctx : Ctx live p q r cx cy ix iy) {j w : Nat} (hw : w ≤ cx.length)
    (imm : BitVec 12)
    (himm : (p + BitVec.ofNat 64 (24 * j)) + sign_extend (m := 64) imm = p + BitVec.ofNat 64 w) :
    ((p + BitVec.ofNat 64 (24 * j)) + sign_extend (m := 64) imm).toNat = p.toNat + w := by
  rw [himm]; exact ctx.wx.ptr p rfl (by omega)

theorem grp_addrY (ctx : Ctx live p q r cx cy ix iy) {j w : Nat} (hw : w ≤ cy.length)
    (imm : BitVec 12)
    (himm : (q + BitVec.ofNat 64 (24 * j)) + sign_extend (m := 64) imm = q + BitVec.ofNat 64 w) :
    ((q + BitVec.ofNat 64 (24 * j)) + sign_extend (m := 64) imm).toNat = q.toNat + w := by
  rw [himm]; exact ctx.wy.ptr q rfl (by omega)

theorem peekW_x {p q : BitVec 64} {w : Nat} {m : Std.ExtHashMap Nat (BitVec 8)}
    {vals : Nat → BitVec 8} (h : ∀ a ∈ peekW p q w, (m[a]?).getD 0 = vals a) :
    ∀ k, k < 8 → (m[p.toNat + w + k]?).getD 0 = vals (p.toNat + w + k) :=
  fun k hk => h _ (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))

theorem peekW_y {p q : BitVec 64} {w : Nat} {m : Std.ExtHashMap Nat (BitVec 8)}
    {vals : Nat → BitVec 8} (h : ∀ a ∈ peekW p q w, (m[a]?).getD 0 = vals a) :
    ∀ k, k < 8 → (m[q.toNat + w + k]?).getD 0 = vals (q.toNat + w + k) :=
  fun k hk => h _ (List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))

/-- **A word-loop group's loads**, for the segment pair `segT` (`x` ends in the
word) and `segF`. The two segments' reflected facts are the instance's. -/
theorem groupLoad (ctx : Ctx live p q r cx cy ix iy) {j w M : Nat} {pc0 pcT pcF : BitVec 64}
    {rv : Nat → BitVec 64} (h : WSt p q r cx cy j w pc0 rv)
    (segT segF : List BBlock) (nT nF : Nat)
    (hlenT : evalBlocksFuel segT = nT + 1) (hlenF : evalBlocksFuel segF = nF + 1)
    (hwfT : ChainOK pc0 cmpRegs segT) (hwfF : ChainOK pc0 cmpRegs segF)
    (hwrT : ∀ k ∈ wrChain segT, k ∈ cmpRegs) (hwrF : ∀ k ∈ wrChain segF, k ∈ cmpRegs)
    (hsT : ∀ vals, (segOut segT (cmpL rv) (ldsW p q w vals)).log = [])
    (hsF : ∀ vals, (segOut segF (cmpL rv) (ldsW p q w vals)).log = [])
    (hfT : ∀ vals, (∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2) → cx.length < w + 8 →
      ∀ m : Std.ExtHashMap Nat (BitVec 8), Code.StrcmpLoaded m →
      (∀ a ∈ peekW p q w, (m[a]?).getD 0 = vals a) → ChainFacts m m (cmpL rv) (ldsW p q w vals) segT)
    (hfF : ∀ vals, (∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2) → w + 8 ≤ cx.length →
      ∀ m : Std.ExtHashMap Nat (BitVec 8), Code.StrcmpLoaded m →
      (∀ a ∈ peekW p q w, (m[a]?).getD 0 = vals a) → ChainFacts m m (cmpL rv) (ldsW p q w vals) segF)
    (hpcT : ∀ vals, evalBlocksPC pc0 (SegEvalState.init (cmpL rv) (ldsW p q w vals)) segT = pcT)
    (hpcF : ∀ vals, evalBlocksPC pc0 (SegEvalState.init (cmpL rv) (ldsW p q w vals)) segF = pcF)
    (hkT : ∀ vals, ∀ k ∈ [1, 7, 10, 11, 15], finReg segT (cmpL rv) (ldsW p q w vals) k = rv k)
    (hkF : ∀ vals, ∀ k ∈ [1, 7, 10, 11, 15], finReg segF (cmpL rv) (ldsW p q w vals) k = rv k)
    (h12T : ∀ vals, finReg segT (cmpL rv) (ldsW p q w vals) 12 = wordAt vals (p.toNat + w))
    (h13T : ∀ vals, finReg segT (cmpL rv) (ldsW p q w vals) 13 = wordAt vals (q.toNat + w))
    (h12F : ∀ vals, finReg segF (cmpL rv) (ldsW p q w vals) 12 = wordAt vals (p.toNat + w))
    (h13F : ∀ vals, finReg segF (cmpL rv) (ldsW p q w vals) 13 = wordAt vals (q.toNat + w))
    (hNul : ∀ A B rv', LSt p q r cx cy j w pcT A B rv' → cx.length < w + 8 →
      CRun live (TT p q cx cy ix iy) r cx cy M rv')
    (hCont : ∀ A B rv', LSt p q r cx cy j w pcF A B rv' → w + 8 ≤ cx.length →
      CRun live (TT p q cx cy ix iy) r cx cy M rv') :
    CRun live (TT p q cx cy ix iy) r cx cy (M + 1) rv := by
  have mk : ∀ (seg : List BBlock) (pc : BitVec 64) (vals : Nat → BitVec 8),
      (∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2) →
      (∀ k ∈ [1, 7, 10, 11, 15], finReg seg (cmpL rv) (ldsW p q w vals) k = rv k) →
      finReg seg (cmpL rv) (ldsW p q w vals) 12 = wordAt vals (p.toNat + w) →
      finReg seg (cmpL rv) (ldsW p q w vals) 13 = wordAt vals (q.toNat + w) →
      ∀ rv', rv' VsaIris.PC = pc →
      (∀ k ∈ cmpRegs, rv' k = finReg seg (cmpL rv) (ldsW p q w vals) k) →
      LSt p q r cx cy j w pc (wordAt vals (p.toNat + w)) (wordAt vals (q.toNat + w)) rv' :=
    fun seg pc vals hv hk h12 h13 rv' hpc hfin =>
      ⟨hpc, by rw [hfin 1 (by decide), hk 1 (by decide)]; exact h.ra,
        by rw [hfin 10 (by decide), hk 10 (by decide)]; exact h.a0,
        by rw [hfin 11 (by decide), hk 11 (by decide)]; exact h.a1,
        by rw [hfin 15 (by decide), hk 15 (by decide)]; exact h.a5,
        by rw [hfin 7 (by decide), hk 7 (by decide)]; exact h.t2,
        by rw [hfin 12 (by decide), h12], by rw [hfin 13 (by decide), h13],
        mkPair ctx hv h.pre, h.le⟩
  by_cases hz : cx.length < w + 8
  · refine cmpStep M ctx.codeL codeT segT (peekW p q w) (ldsW p q w) pc0 nT hlenT hwfT hwrT hsT
      h.pc (fun vals hv m hl hpk => hfT vals hv hz m hl hpk) ?_
    intro vals hv rv' hpc hfin
    exact hNul _ _ rv' (mk segT pcT vals hv (hkT vals) (h12T vals) (h13T vals) rv'
      (hpc.trans (hpcT vals)) hfin) hz
  · refine cmpStep M ctx.codeL codeT segF (peekW p q w) (ldsW p q w) pc0 nF hlenF hwfF hwrF hsF
      h.pc (fun vals hv m hl hpk => hfF vals hv (by omega) m hl hpk) ?_
    intro vals hv rv' hpc hfin
    exact hCont _ _ rv' (mk segF pcF vals hv (hkF vals) (h12F vals) (h13F vals) rv'
      (hpc.trans (hpcF vals)) hfin) (by omega)

/-! ## The NUL-word exits (`0x80006fa4 … 0x80006fc8`)

`x`'s word holds its NUL. The pointers advance to the word, and `bne a2,a3`
re-tests the words: equal words mean equal strings (`li a0,0; ret`); different
words run the byte loop from the word. -/

/-- `li a0,0; ret` (`0x80006fb0`). -/
theorem ret_fb0 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64}
    (hpc : rv VsaIris.PC = 0x80006fb0#64) (hra : rv 1 = r) (hs : strcmpSpecSign cx cy = 0) :
    CRun live (TT p q cx cy ix iy) r cx cy 1 rv := by
  refine cmpStep 0 ctx.codeL codeT strcmpX6fb0Seg [] (fun _ => []) _ _ rfl (by decide)
    (by decide) (fun _ => rfl) hpc ?_ ?_
  · intro vals _ m hl _
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    change (Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [hra, ret_tgt r ctx.ret]; exact ctx.ret
  · intro vals _ rv' hpc' hfin
    refine CRun.done ⟨?_, ?_, ?_⟩
    · rw [hpc']
      show Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1 = r
      rw [hra, ret_tgt r ctx.ret]
    · rw [hfin 1 (by decide)]; exact hra
    · rw [hfin 10 (by decide), hs, show finReg strcmpX6fb0Seg (cmpL rv) [] 10 = 0#64 from rfl]
      rfl

/-- `li a0,0; ret` (`0x80006fc4`). -/
theorem ret_fc4 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64}
    (hpc : rv VsaIris.PC = 0x80006fc4#64) (hra : rv 1 = r) (hs : strcmpSpecSign cx cy = 0) :
    CRun live (TT p q cx cy ix iy) r cx cy 1 rv := by
  refine cmpStep 0 ctx.codeL codeT strcmpX6fc4Seg [] (fun _ => []) _ _ rfl (by decide)
    (by decide) (fun _ => rfl) hpc ?_ ?_
  · intro vals _ m hl _
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    change (Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [hra, ret_tgt r ctx.ret]; exact ctx.ret
  · intro vals _ rv' hpc' hfin
    refine CRun.done ⟨?_, ?_, ?_⟩
    · rw [hpc']
      show Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0x000#12)) 0 0#1 = r
      rw [hra, ret_tgt r ctx.ret]
    · rw [hfin 1 (by decide)]; exact hra
    · rw [hfin 10 (by decide), hs, show finReg strcmpX6fc4Seg (cmpL rv) [] 10 = 0#64 from rfl]
      rfl

/-- At a NUL-word re-test: the pointers at the word `w`, the words in `a2`/`a3`. -/
structure NSt (p q r : BitVec 64) (cx cy : List Char) (w : Nat) (A B : BitVec 64)
    (rv : Nat → BitVec 64) : Prop where
  ra : rv 1 = r
  a0 : rv 10 = p + BitVec.ofNat 64 w
  a1 : rv 11 = q + BitVec.ofNat 64 w
  a2 : rv 12 = A
  a3 : rv 13 = B
  pair : WordPair cx cy w A B
  le : w ≤ cx.length
  lt : cx.length < w + 8

/-- The re-test at `0x80006fac`. -/
theorem nulFac (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64} {w : Nat}
    {A B : BitVec 64} (hpc : rv VsaIris.PC = 0x80006fac#64) (h : NSt p q r cx cy w A B rv) :
    CRun live (TT p q cx cy ix iy) r cx cy (3 * (cx.length - w) + 4) rv := by
  by_cases he : A = B
  · refine CRun.mono (by omega : 2 ≤ _) ?_
    refine cmpStep 1 ctx.codeL codeT strcmpX6facFSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 != rv 13) = false
      rw [h.a2, h.a3, he]; simp
    · intro vals _ rv' hpc' hfin
      exact ret_fb0 ctx hpc' ((hfin 1 (by decide)).trans h.ra)
        (h.pair.nul_eq ctx.bx ctx.by_ h.le h.lt he)
  · refine cmpStep _ ctx.codeL codeT strcmpX6facTSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 != rv 13) = true
      rw [h.a2, h.a3, bne_iff_ne]; exact he
    · intro vals _ rv' hpc' hfin
      exact byteLoop ctx _ w rv' rfl ⟨hpc', (hfin 1 (by decide)).trans h.ra,
        (hfin 10 (by decide)).trans h.a0, (hfin 11 (by decide)).trans h.a1, h.pair.pre⟩

/-- Group 1's exit (`0x80006fa4`): advance by 8, then the re-test. -/
theorem nulFa4 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64} {j : Nat}
    {A B : BitVec 64} (h : LSt p q r cx cy j (24 * j + 8) 0x80006fa4#64 A B rv)
    (hlt : cx.length < 24 * j + 8 + 8) :
    CRun live (TT p q cx cy ix iy) r cx cy (3 * (cx.length - (24 * j + 8)) + 5) rv := by
  refine cmpStep _ ctx.codeL codeT strcmpX6fa4Seg [] (fun _ => []) _ _ rfl (by decide)
    (by decide) (fun _ => rfl) h.pc ?_ ?_
  · intro vals _ m hl _
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
  · intro vals _ rv' hpc' hfin
    refine nulFac ctx hpc' ⟨(hfin 1 (by decide)).trans h.ra, ?_, ?_,
      (hfin 12 (by decide)).trans h.a2, (hfin 13 (by decide)).trans h.a3, h.pair, h.le, hlt⟩
    · rw [hfin 10 (by decide)]; show rv 10 + sign_extend (m := 64) (0x008#12) = _; rw [h.a0, word_off8]
    · rw [hfin 11 (by decide)]; show rv 11 + sign_extend (m := 64) (0x008#12) = _; rw [h.a1, word_off8]

/-- Group 2's exit (`0x80006fb8`): advance by 16 and re-test. -/
theorem nulFb8 (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64} {j : Nat}
    {A B : BitVec 64} (h : LSt p q r cx cy j (24 * j + 16) 0x80006fb8#64 A B rv)
    (hlt : cx.length < 24 * j + 16 + 8) :
    CRun live (TT p q cx cy ix iy) r cx cy (3 * (cx.length - (24 * j + 16)) + 4) rv := by
  have e10 : rv 10 + sign_extend (m := 64) (0x010#12) = p + BitVec.ofNat 64 (24 * j + 16) := by
    rw [h.a0, word_off16]
  have e11 : rv 11 + sign_extend (m := 64) (0x010#12) = q + BitVec.ofNat 64 (24 * j + 16) := by
    rw [h.a1, word_off16]
  by_cases he : A = B
  · refine CRun.mono (by omega : 2 ≤ _) ?_
    refine cmpStep 1 ctx.codeL codeT strcmpX6fb8FSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 != rv 13) = false
      rw [h.a2, h.a3, he]; simp
    · intro vals _ rv' hpc' hfin
      exact ret_fc4 ctx hpc' ((hfin 1 (by decide)).trans h.ra)
        (h.pair.nul_eq ctx.bx ctx.by_ h.le hlt he)
  · refine cmpStep _ ctx.codeL codeT strcmpX6fb8TSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 != rv 13) = true
      rw [h.a2, h.a3, bne_iff_ne]; exact he
    · intro vals _ rv' hpc' hfin
      exact byteLoop ctx _ _ rv' rfl ⟨hpc', (hfin 1 (by decide)).trans h.ra,
        (hfin 10 (by decide)).trans e10, (hfin 11 (by decide)).trans e11, h.pair.pre⟩

/-- A group's two `ld`s and its `bne t0,t2`, closed from the loaded pair. -/
theorem grp_ld_facts (ctx : Ctx live p q r cx cy ix iy) {j w : Nat} {pc0 : BitVec 64}
    {rv : Nat → BitVec 64} (h : WSt p q r cx cy j w pc0 rv) :
    (0x80000000 ≤ p.toNat + w ∧ p.toNat + w + 8 ≤ 0x100000000 ∧
      (p.toNat + w + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat + w)) ∧
    (0x80000000 ≤ q.toNat + w ∧ q.toNat + w + 8 ≤ 0x100000000 ∧
      (q.toNat + w + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ q.toNat + w)) :=
  ⟨ctx.wx.ld (by have := h.le; omega),
   ctx.wy.ld (by have := h.le; have := prefix_le_lenb h.pre; omega)⟩

/-- Words differ after a `bne a2,a3` (`0x80006ed4`): the lane compare; or the
next group at `0x80006ed8`. -/
theorem cmpEd4 (ctx : Ctx live p q r cx cy ix iy) {j w : Nat} {A B : BitVec 64}
    {rv : Nat → BitVec 64} (h : LSt p q r cx cy j w 0x80006ed4#64 A B rv)
    (hw8 : w + 8 ≤ cx.length) (M : Nat) (h6 : 6 ≤ M)
    (hk : ∀ rv', WSt p q r cx cy j (w + 8) 0x80006ed8#64 rv' →
      CRun live (TT p q cx cy ix iy) r cx cy M rv') :
    CRun live (TT p q cx cy ix iy) r cx cy (M + 1) rv := by
  by_cases he : A = B
  · refine cmpStep M ctx.codeL codeT strcmpX6ed4FSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 != rv 13) = false
      rw [h.a2, h.a3, he]; simp
    · intro vals _ rv' hpc' hfin
      exact hk rv' ⟨hpc', (hfin 1 (by decide)).trans h.ra, (hfin 10 (by decide)).trans h.a0,
        (hfin 11 (by decide)).trans h.a1, (hfin 15 (by decide)).trans h.a5,
        (hfin 7 (by decide)).trans h.t2, h.pair.eq_next ctx.bx hw8 he, hw8⟩
  · obtain ⟨d, hd⟩ := h.pair.lane ctx.bx ctx.by_ hw8 he
    refine cmpStep M ctx.codeL codeT strcmpX6ed4TSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 != rv 13) = true
      rw [h.a2, h.a3, bne_iff_ne]; exact he
    · intro vals _ rv' hpc' hfin
      exact (laneRun ctx hpc' ((hfin 1 (by decide)).trans h.ra) ((hfin 12 (by decide)).trans h.a2)
        ((hfin 13 (by decide)).trans h.a3) hd).mono h6

/-- The same at `0x80006ef4`, to the group at `0x80006ef8`. -/
theorem cmpEf4 (ctx : Ctx live p q r cx cy ix iy) {j w : Nat} {A B : BitVec 64}
    {rv : Nat → BitVec 64} (h : LSt p q r cx cy j w 0x80006ef4#64 A B rv)
    (hw8 : w + 8 ≤ cx.length) (M : Nat) (h6 : 6 ≤ M)
    (hk : ∀ rv', WSt p q r cx cy j (w + 8) 0x80006ef8#64 rv' →
      CRun live (TT p q cx cy ix iy) r cx cy M rv') :
    CRun live (TT p q cx cy ix iy) r cx cy (M + 1) rv := by
  by_cases he : A = B
  · refine cmpStep M ctx.codeL codeT strcmpX6ef4FSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 != rv 13) = false
      rw [h.a2, h.a3, he]; simp
    · intro vals _ rv' hpc' hfin
      exact hk rv' ⟨hpc', (hfin 1 (by decide)).trans h.ra, (hfin 10 (by decide)).trans h.a0,
        (hfin 11 (by decide)).trans h.a1, (hfin 15 (by decide)).trans h.a5,
        (hfin 7 (by decide)).trans h.t2, h.pair.eq_next ctx.bx hw8 he, hw8⟩
  · obtain ⟨d, hd⟩ := h.pair.lane ctx.bx ctx.by_ hw8 he
    refine cmpStep M ctx.codeL codeT strcmpX6ef4TSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 != rv 13) = true
      rw [h.a2, h.a3, bne_iff_ne]; exact he
    · intro vals _ rv' hpc' hfin
      exact (laneRun ctx hpc' ((hfin 1 (by decide)).trans h.ra) ((hfin 12 (by decide)).trans h.a2)
        ((hfin 13 (by decide)).trans h.a3) hd).mono h6

/-- The back edge (`0x80006f14`: advance by 24, `beq a2,a3`): the next
iteration's group 0, or the lane compare. -/
theorem cmpF14 (ctx : Ctx live p q r cx cy ix iy) {j : Nat} {A B : BitVec 64}
    {rv : Nat → BitVec 64} (h : LSt p q r cx cy j (24 * j + 16) 0x80006f14#64 A B rv)
    (hw8 : 24 * j + 16 + 8 ≤ cx.length) (M : Nat) (h6 : 6 ≤ M)
    (hk : ∀ rv', WSt p q r cx cy (j + 1) (24 * (j + 1)) 0x80006eb8#64 rv' →
      CRun live (TT p q cx cy ix iy) r cx cy M rv') :
    CRun live (TT p q cx cy ix iy) r cx cy (M + 1) rv := by
  by_cases he : A = B
  · refine cmpStep M ctx.codeL codeT strcmpX6f14TSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 == rv 13) = true
      rw [h.a2, h.a3, he]; simp
    · intro vals _ rv' hpc' hfin
      refine hk rv' ⟨hpc', (hfin 1 (by decide)).trans h.ra, ?_, ?_,
        (hfin 15 (by decide)).trans h.a5, (hfin 7 (by decide)).trans h.t2,
        by rw [show 24 * (j + 1) = 24 * j + 16 + 8 by omega]; exact h.pair.eq_next ctx.bx hw8 he,
        by omega⟩
      · rw [hfin 10 (by decide)]; show rv 10 + sign_extend (m := 64) (0x018#12) = _
        rw [h.a0, word_off24]
      · rw [hfin 11 (by decide)]; show rv 11 + sign_extend (m := 64) (0x018#12) = _
        rw [h.a1, word_off24]
  · obtain ⟨d, hd⟩ := h.pair.lane ctx.bx ctx.by_ hw8 he
    refine cmpStep M ctx.codeL codeT strcmpX6f14FSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) h.pc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (rv 12 == rv 13) = false
      rw [h.a2, h.a3]; simpa using he
    · intro vals _ rv' hpc' hfin
      exact (laneRun ctx hpc' ((hfin 1 (by decide)).trans h.ra) ((hfin 12 (by decide)).trans h.a2)
        ((hfin 13 (by decide)).trans h.a3) hd).mono h6

/-- The fuel of the word loop at offset `w`. -/
abbrev fuelW (cx : List Char) (w : Nat) : Nat := 3 * (cx.length - w) + 8

/-- **Group 0** (`0x80006eb8`, offset `24j`). -/
theorem group0 (ctx : Ctx live p q r cx cy ix iy) {j : Nat} {rv : Nat → BitVec 64}
    (h : WSt p q r cx cy j (24 * j) 0x80006eb8#64 rv)
    (hk : ∀ rv', WSt p q r cx cy j (24 * j + 8) 0x80006ed8#64 rv' →
      CRun live (TT p q cx cy ix iy) r cx cy (fuelW cx (24 * j + 8)) rv') :
    CRun live (TT p q cx cy ix iy) r cx cy (fuelW cx (24 * j)) rv := by
  obtain ⟨hlx, hly⟩ := grp_ld_facts ctx h
  have ax : ((rv 10) + sign_extend (m := 64) (0x000#12)).toNat = p.toNat + 24 * j := by
    rw [sext0_add, h.a0]; exact ctx.wx.ptr p rfl (by have := h.le; omega)
  have ay : ((rv 11) + sign_extend (m := 64) (0x000#12)).toNat = q.toNat + 24 * j := by
    rw [sext0_add, h.a1]
    exact ctx.wy.ptr q rfl (by have := h.le; have := prefix_le_lenb h.pre; omega)
  refine groupLoad ctx (M := 3 * (cx.length - 24 * j) + 7) h strcmpX6eb8TSeg strcmpX6eb8FSeg
    _ _ rfl rfl (by decide) (by decide) (by decide) (by decide) (fun _ => rfl) (fun _ => rfl)
    ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ k hk => ?_) (fun _ k hk => ?_)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_
  · intro vals hv hz m hl hpk
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    · exact ldF rfl vals ax hlx.1 hlx.2.1 hlx.2.2 (peekW_x hpk)
    · exact ldF rfl vals ay hly.1 hly.2.1 hly.2.2 (peekW_y hpk)
    · change ((((wordAt vals (p.toNat + 24 * j) &&& rv 15) + rv 15) |||
        (wordAt vals (p.toNat + 24 * j) ||| rv 15)) != rv 7) = true
      rw [grp_guard ctx (mkPair ctx hv h.pre) h.le h.a5 h.t2]; simpa using hz
  · intro vals hv hz m hl hpk
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    · exact ldF rfl vals ax hlx.1 hlx.2.1 hlx.2.2 (peekW_x hpk)
    · exact ldF rfl vals ay hly.1 hly.2.1 hly.2.2 (peekW_y hpk)
    · change ((((wordAt vals (p.toNat + 24 * j) &&& rv 15) + rv 15) |||
        (wordAt vals (p.toNat + 24 * j) ||| rv 15)) != rv 7) = false
      rw [grp_guard ctx (mkPair ctx hv h.pre) h.le h.a5 h.t2]; simp; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro A B rv' h' hz
    exact (nulFac ctx h'.pc ⟨h'.ra, by rw [h'.a0], by rw [h'.a1], h'.a2, h'.a3, h'.pair, h'.le,
      hz⟩).mono (by omega)
  · intro A B rv' h' hw8
    refine (cmpEd4 ctx h' hw8 (3 * (cx.length - 24 * j) + 6) (by omega) fun rv'' h'' => ?_).mono
      (by omega)
    exact (hk rv'' h'').mono (by unfold fuelW; omega)

/-- **Group 1** (`0x80006ed8`, offset `24j + 8`). -/
theorem group1 (ctx : Ctx live p q r cx cy ix iy) {j : Nat} {rv : Nat → BitVec 64}
    (h : WSt p q r cx cy j (24 * j + 8) 0x80006ed8#64 rv)
    (hk : ∀ rv', WSt p q r cx cy j (24 * j + 8 + 8) 0x80006ef8#64 rv' →
      CRun live (TT p q cx cy ix iy) r cx cy (fuelW cx (24 * j + 8 + 8)) rv') :
    CRun live (TT p q cx cy ix iy) r cx cy (fuelW cx (24 * j + 8)) rv := by
  obtain ⟨hlx, hly⟩ := grp_ld_facts ctx h
  have ax : ((rv 10) + sign_extend (m := 64) (0x008#12)).toNat = p.toNat + (24 * j + 8) := by
    rw [h.a0, word_off8]; exact ctx.wx.ptr p rfl (by have := h.le; omega)
  have ay : ((rv 11) + sign_extend (m := 64) (0x008#12)).toNat = q.toNat + (24 * j + 8) := by
    rw [h.a1, word_off8]
    exact ctx.wy.ptr q rfl (by have := h.le; have := prefix_le_lenb h.pre; omega)
  refine groupLoad ctx (M := 3 * (cx.length - (24 * j + 8)) + 7) h strcmpX6ed8TSeg
    strcmpX6ed8FSeg _ _ rfl rfl (by decide) (by decide) (by decide) (by decide) (fun _ => rfl)
    (fun _ => rfl) ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ k hk => ?_) (fun _ k hk => ?_)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_
  · intro vals hv hz m hl hpk
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    · exact ldF rfl vals ax hlx.1 hlx.2.1 hlx.2.2 (peekW_x hpk)
    · exact ldF rfl vals ay hly.1 hly.2.1 hly.2.2 (peekW_y hpk)
    · change ((((wordAt vals (p.toNat + (24 * j + 8)) &&& rv 15) + rv 15) |||
        (wordAt vals (p.toNat + (24 * j + 8)) ||| rv 15)) != rv 7) = true
      rw [grp_guard ctx (mkPair ctx hv h.pre) h.le h.a5 h.t2]; simpa using hz
  · intro vals hv hz m hl hpk
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    · exact ldF rfl vals ax hlx.1 hlx.2.1 hlx.2.2 (peekW_x hpk)
    · exact ldF rfl vals ay hly.1 hly.2.1 hly.2.2 (peekW_y hpk)
    · change ((((wordAt vals (p.toNat + (24 * j + 8)) &&& rv 15) + rv 15) |||
        (wordAt vals (p.toNat + (24 * j + 8)) ||| rv 15)) != rv 7) = false
      rw [grp_guard ctx (mkPair ctx hv h.pre) h.le h.a5 h.t2]; simp; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro A B rv' h' hz
    exact (nulFa4 ctx h' hz).mono (by omega)
  · intro A B rv' h' hw8
    refine (cmpEf4 ctx h' hw8 (3 * (cx.length - (24 * j + 8)) + 6) (by omega)
      fun rv'' h'' => ?_).mono (by omega)
    exact (hk rv'' h'').mono (by unfold fuelW; omega)

/-- **Group 2** (`0x80006ef8`, offset `24j + 16`). -/
theorem group2 (ctx : Ctx live p q r cx cy ix iy) {j : Nat} {rv : Nat → BitVec 64}
    (h : WSt p q r cx cy j (24 * j + 16) 0x80006ef8#64 rv)
    (hk : ∀ rv', WSt p q r cx cy (j + 1) (24 * (j + 1)) 0x80006eb8#64 rv' →
      CRun live (TT p q cx cy ix iy) r cx cy (fuelW cx (24 * (j + 1))) rv') :
    CRun live (TT p q cx cy ix iy) r cx cy (fuelW cx (24 * j + 16)) rv := by
  obtain ⟨hlx, hly⟩ := grp_ld_facts ctx h
  have ax : ((rv 10) + sign_extend (m := 64) (0x010#12)).toNat = p.toNat + (24 * j + 16) := by
    rw [h.a0, word_off16]; exact ctx.wx.ptr p rfl (by have := h.le; omega)
  have ay : ((rv 11) + sign_extend (m := 64) (0x010#12)).toNat = q.toNat + (24 * j + 16) := by
    rw [h.a1, word_off16]
    exact ctx.wy.ptr q rfl (by have := h.le; have := prefix_le_lenb h.pre; omega)
  refine groupLoad ctx (M := 3 * (cx.length - (24 * j + 16)) + 7) h strcmpX6ef8TSeg
    strcmpX6ef8FSeg _ _ rfl rfl (by decide) (by decide) (by decide) (by decide) (fun _ => rfl)
    (fun _ => rfl) ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ k hk => ?_) (fun _ k hk => ?_)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_
  · intro vals hv hz m hl hpk
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    · exact ldF rfl vals ax hlx.1 hlx.2.1 hlx.2.2 (peekW_x hpk)
    · exact ldF rfl vals ay hly.1 hly.2.1 hly.2.2 (peekW_y hpk)
    · change ((((wordAt vals (p.toNat + (24 * j + 16)) &&& rv 15) + rv 15) |||
        (wordAt vals (p.toNat + (24 * j + 16)) ||| rv 15)) != rv 7) = true
      rw [grp_guard ctx (mkPair ctx hv h.pre) h.le h.a5 h.t2]; simpa using hz
  · intro vals hv hz m hl hpk
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    · exact ldF rfl vals ax hlx.1 hlx.2.1 hlx.2.2 (peekW_x hpk)
    · exact ldF rfl vals ay hly.1 hly.2.1 hly.2.2 (peekW_y hpk)
    · change ((((wordAt vals (p.toNat + (24 * j + 16)) &&& rv 15) + rv 15) |||
        (wordAt vals (p.toNat + (24 * j + 16)) ||| rv 15)) != rv 7) = false
      rw [grp_guard ctx (mkPair ctx hv h.pre) h.le h.a5 h.t2]; simp; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro A B rv' h' hz
    exact (nulFb8 ctx h' hz).mono (by omega)
  · intro A B rv' h' hw8
    refine (cmpF14 ctx h' hw8 (3 * (cx.length - (24 * j + 16)) + 6) (by omega)
      fun rv'' h'' => ?_).mono (by omega)
    exact (hk rv'' h'').mono (by unfold fuelW; omega)

/-- **The word loop** from iteration `j`'s group 0. -/
theorem wordLoop (ctx : Ctx live p q r cx cy ix iy) :
    ∀ (n j : Nat) (rv : Nat → BitVec 64), cx.length - 24 * j ≤ n →
      WSt p q r cx cy j (24 * j) 0x80006eb8#64 rv →
      CRun live (TT p q cx cy ix iy) r cx cy (fuelW cx (24 * j)) rv := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j rv hn h
    refine group0 ctx h fun rv1 h1 => group1 ctx h1 fun rv2 h2 => group2 ctx h2 fun rv3 h3 => ?_
    exact ih (cx.length - 24 * (j + 1)) (by have := h2.le; omega) (j + 1) rv3 (Nat.le_refl _) h3

/-! ## Entry (`0x80006ea0 … 0x80006eb4`) and the whole function -/

theorem mask_word : bytesVal .ld (List.replicate 8 0x7f#8) = magic7f := by decide

theorem valsMask {vals : Nat → BitVec 8} (hv : ∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2) :
    bytesAt vals 0x8001ac80 8 = List.replicate 8 0x7f#8 := by
  have hm : ∀ k, k < 8 → vals (0x8001ac80 + k) = 0x7f#8 := fun k hk =>
    hv (0x8001ac80 + k, 0x7f#8) (by
      unfold TT cmpText
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append]
  rw [hm 0 (by omega), hm 1 (by omega), hm 2 (by omega), hm 3 (by omega), hm 4 (by omega),
    hm 5 (by omega), hm 6 (by omega), hm 7 (by omega)]
  rfl

/-- The aligned entry's mask load (`0x80006eb0`): group 0 of iteration 0. -/
theorem entryMask (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64}
    (hpc : rv VsaIris.PC = 0x80006eb0#64) (hra : rv 1 = r) (h10 : rv 10 = p) (h11 : rv 11 = q)
    (h7 : rv 7 = -1#64) :
    CRun live (TT p q cx cy ix iy) r cx cy (fuelW cx 0 + 1) rv := by
  refine cmpStep _ ctx.codeL codeT strcmpX6eb0Seg ((List.range 8).map (0x8001ac80 + ·))
    (fun vals => [bytesAt vals 0x8001ac80 8]) _ _ rfl (by decide) (by decide) (fun _ => rfl)
    hpc ?_ ?_
  · intro vals _ m hl hpk
    chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
    refine ldF rfl vals ?_ (by omega) (by omega) (Or.inl (by rw [show tohostAddr = 0x8001ad00 from rfl]; omega))
      (fun k hk => hpk _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
    show ((0x80006eb0#64 + sign_extend (m := 64) ((0x00014#20) ++ 0x000#12)) +
      sign_extend (m := 64) (0xdd0#12)).toNat = _
    decide
  · intro vals hv rv' hpc' hfin
    have e15 : rv' 15 = magic7f := by
      rw [hfin 15 (by decide)]
      show bytesVal .ld (bytesAt vals 0x8001ac80 8) = _
      rw [valsMask hv]; exact mask_word
    refine wordLoop ctx (cx.length - 24 * 0) 0 rv' (Nat.le_refl _) ⟨hpc', ?_, ?_, ?_, e15, ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _), Nat.zero_le _⟩
    · rw [hfin 1 (by decide)]; exact hra
    · rw [hfin 10 (by decide)]; show rv 10 = _; rw [h10]; simp
    · rw [hfin 11 (by decide)]; show rv 11 = _; rw [h11]; simp
    · rw [hfin 7 (by decide)]; exact h7

/-- **`strcmp` as one run**: from the entry with `a0 = p`, `a1 = q` and `ra = r`,
it returns to `r` with the sign of the byte-lexicographic comparison in `a0`. -/
theorem strcmpRun (ctx : Ctx live p q r cx cy ix iy) {rv : Nat → BitVec 64}
    (hpc : rv VsaIris.PC = 0x80006ea0#64) (hra : rv 1 = r) (h10 : rv 10 = p) (h11 : rv 11 = q) :
    CRun live (TT p q cx cy ix iy) r cx cy (3 * cx.length + 11) rv := by
  by_cases hal : ((rv 10 ||| rv 11) &&& sign_extend (m := 64) (0x007#12)) = 0#64
  · refine cmpStep _ ctx.codeL codeT strcmpX6ea0FSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (((rv 10 ||| rv 11) &&& sign_extend (m := 64) (0x007#12)) != 0#64) = false
      rw [hal]; rfl
    · intro vals _ rv' hpc' hfin
      refine (entryMask ctx hpc' ((hfin 1 (by decide)).trans hra) ((hfin 10 (by decide)).trans h10)
        ((hfin 11 (by decide)).trans h11) ?_).mono (by unfold fuelW; omega)
      rw [hfin 7 (by decide)]
      show (0#64 : BitVec 64) + sign_extend (m := 64) (0xfff#12) = -1#64
      decide
  · refine cmpStep _ ctx.codeL codeT strcmpX6ea0TSeg [] (fun _ => []) _ _ rfl (by decide)
      (by decide) (fun _ => rfl) hpc ?_ ?_
    · intro vals _ m hl _
      chain_facts hl with "Vsa.Sim.Code.strcmp_at_"
      change (((rv 10 ||| rv 11) &&& sign_extend (m := 64) (0x007#12)) != 0#64) = true
      rw [bne_iff_ne]; exact hal
    · intro vals _ rv' hpc' hfin
      refine (byteLoop ctx cx.length 0 rv' (by omega) ⟨hpc', (hfin 1 (by decide)).trans hra,
        ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩).mono (by omega)
      · rw [hfin 10 (by decide)]; show rv 10 = _; rw [h10]; simp
      · rw [hfin 11 (by decide)]; show rv 11 = _; rw [h11]; simp

end Loop

end VsaIris.Inst.Strcmp

#print axioms VsaIris.Inst.Strcmp.strcmpRun

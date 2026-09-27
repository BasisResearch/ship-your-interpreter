import Vsa.Compiler.Frag

/-!
# A verification-condition generator for abstract-machine code

`WP code P pos is K L m o` is the weakest precondition of running the
instruction list `is`, placed at index `pos` of `code`, from registers `L`,
memory `m`, and console `o`: straight-line instructions update the state,
a branch either continues or must reach `P` from its target, a jump must reach
`P` from its target, and falling off the end hands the state to `K`.
`WP_sound` turns it into a run. `simp only [WP]` computes it symbolically; the
side conditions it leaves (register availability, address windows, the branch
guards) are the whole proof obligation of a straight-line fragment.
-/

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim

/-- Target index of a branch at `pos` with byte offset `off`. -/
def brT (pos : Nat) (off : BitVec 13) : Nat := ((pos : Int) + off.toInt / 4).toNat

/-- Target index of a jump at `pos` with byte offset `off`. -/
def jT (pos : Nat) (off : BitVec 21) : Nat := ((pos : Int) + off.toInt / 4).toNat

/-- The branch offset reaches instruction `t` from `pos` inside the code window. -/
def BrOK (pos : Nat) (off : BitVec 13) : Prop :=
  off.toInt % 4 = 0 ∧ 0 ≤ (pos : Int) + off.toInt / 4 ∧ PosOK (brT pos off)

/-- The jump offset reaches instruction `t` from `pos` inside the code window. -/
def JOK (pos : Nat) (off : BitVec 21) : Prop :=
  off.toInt % 4 = 0 ∧ 0 ≤ (pos : Int) + off.toInt / 4 ∧ PosOK (jT pos off)

/-- Absolute target address of a `jal` at `pos` with byte offset `off`. -/
def libAddr (pos : Nat) (off : BitVec 21) : Nat := (((codeBase + 4 * pos : Nat) : Int) + off.toInt).toNat

/-- The `jal` at `pos` calls one of libgcc's routines. -/
def isLib (pos : Nat) (off : BitVec 21) : Bool :=
  off.toNat % 2 == 0 && (libAddr pos off == mulPC || libAddr pos off == divPC || libAddr pos off == modPC)

/-- Weakest precondition of an instruction list (see the module doc). -/
def WP (code : List Ins) (P : AM → Prop) (pos : Nat) :
    List Ins → (GRegs → Mem → Array String → Prop) → GRegs → Mem → Array String → Prop
  | [], K, L, m, o => K L m o
  | i :: is, K, L, m, o =>
    match i with
    | .addi rd rs imm => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs (keysG L) ∧
        WP code P (pos + 1) is K (gset L rd (srcVal rs L + sign_extend imm)) m o
    | .ori rd rs imm => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs (keysG L) ∧
        WP code P (pos + 1) is K (gset L rd (srcVal rs L ||| sign_extend imm)) m o
    | .slli rd rs sh => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs (keysG L) ∧
        WP code P (pos + 1) is K (gset L rd (srcVal rs L <<< sh.toNat)) m o
    | .add rd r1 r2 => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK r1 (keysG L) ∧ SrcOK r2 (keysG L) ∧
        WP code P (pos + 1) is K (gset L rd (srcVal r1 L + srcVal r2 L)) m o
    | .sub rd r1 r2 => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK r1 (keysG L) ∧ SrcOK r2 (keysG L) ∧
        WP code P (pos + 1) is K (gset L rd (srcVal r1 L - srcVal r2 L)) m o
    | .ld rd rs => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs (keysG L) ∧ LdOK (srcVal rs L).toNat ∧
        WP code P (pos + 1) is K (gset L rd (rdW m (srcVal rs L).toNat)) m o
    | .sd rs2 rs1 => SrcOK rs1 (keysG L) ∧ SrcOK rs2 (keysG L) ∧
        (if (srcVal rs1 L).toNat = tohostAddr then
          srcVal rs2 L = putcWord ((srcVal rs2 L).setWidth 8) ∧
          WP code P (pos + 1) is K L m
            (o.push (toString (Char.ofNat ((srcVal rs2 L).setWidth 8).toNat)))
        else StOK (srcVal rs1 L).toNat ∧
          WP code P (pos + 1) is K L (applyW m ((srcVal rs1 L).toNat, 8, srcVal rs2 L)) o)
    | .br op r1 r2 off => SrcOK r1 (keysG L) ∧ SrcOK r2 (keysG L) ∧ BrOK pos off ∧
        (if guardB op.bop (srcVal r1 L) (srcVal r2 L) then
          Reaches code ⟨pcOf (brT pos off), L, m, o⟩ P
        else WP code P (pos + 1) is K L m o)
    | .jal rd off =>
      if rd = 0 then JOK pos off ∧ Reaches code ⟨pcOf (jT pos off), L, m, o⟩ P
      else if rd = 1 then
        if isLib pos off then
          SrcOK 10 (keysG L) ∧ SrcOK 11 (keysG L) ∧ 12 ∈ keysG L ∧ 13 ∈ keysG L ∧
          (match libRes (libAddr pos off) (srcVal 10 L) (srcVal 11 L) with
            | some r => WP code P (pos + 1) is K ((10, r) :: eraseAll clobbered L) m o
            | none => False)
        else JOK pos off ∧
          Reaches code ⟨pcOf (jT pos off), gset L 1 (pcOf (pos + 1)), m, o⟩ P
      else False
    | .jalr rs => SrcOK rs (keysG L) ∧ (srcVal rs L).toNat % 4 = 0 ∧
        Reaches code ⟨srcVal rs L, L, m, o⟩ P

section WPEq
variable {code : List Ins} {P : AM → Prop} {pos : Nat} {is : List Ins}
  {K : GRegs → Mem → Array String → Prop} {L : GRegs} {m : Mem} {o : Array String}

/-! Equations of `WP`, one per instruction form. `wp_simp` rewrites with these
instead of unfolding `WP`. The equations are proved propositionally, so simp
uses them as rewrites rather than definitional unfoldings, and the kernel never
reduces `WP` (and with it jump offsets) on symbolic positions. -/

theorem WP_nil : WP code P pos [] K L m o = K L m o := by rw [WP]
theorem WP_addi {rd rs imm} : WP code P pos (.addi rd rs imm :: is) K L m o =
    ((1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs (keysG L) ∧
      WP code P (pos + 1) is K (gset L rd (srcVal rs L + sign_extend imm)) m o) := by rw [WP]
theorem WP_ori {rd rs imm} : WP code P pos (.ori rd rs imm :: is) K L m o =
    ((1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs (keysG L) ∧
      WP code P (pos + 1) is K (gset L rd (srcVal rs L ||| sign_extend imm)) m o) := by rw [WP]
theorem WP_slli {rd rs sh} : WP code P pos (.slli rd rs sh :: is) K L m o =
    ((1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs (keysG L) ∧
      WP code P (pos + 1) is K (gset L rd (srcVal rs L <<< sh.toNat)) m o) := by rw [WP]
theorem WP_add {rd r1 r2} : WP code P pos (.add rd r1 r2 :: is) K L m o =
    ((1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK r1 (keysG L) ∧ SrcOK r2 (keysG L) ∧
      WP code P (pos + 1) is K (gset L rd (srcVal r1 L + srcVal r2 L)) m o) := by rw [WP]
theorem WP_sub {rd r1 r2} : WP code P pos (.sub rd r1 r2 :: is) K L m o =
    ((1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK r1 (keysG L) ∧ SrcOK r2 (keysG L) ∧
      WP code P (pos + 1) is K (gset L rd (srcVal r1 L - srcVal r2 L)) m o) := by rw [WP]
theorem WP_ld {rd rs} : WP code P pos (.ld rd rs :: is) K L m o =
    ((1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs (keysG L) ∧ LdOK (srcVal rs L).toNat ∧
      WP code P (pos + 1) is K (gset L rd (rdW m (srcVal rs L).toNat)) m o) := by rw [WP]
theorem WP_sd {rs2 rs1} : WP code P pos (.sd rs2 rs1 :: is) K L m o =
    (SrcOK rs1 (keysG L) ∧ SrcOK rs2 (keysG L) ∧
      (if (srcVal rs1 L).toNat = tohostAddr then
        srcVal rs2 L = putcWord ((srcVal rs2 L).setWidth 8) ∧
        WP code P (pos + 1) is K L m (o.push (toString (Char.ofNat ((srcVal rs2 L).setWidth 8).toNat)))
      else StOK (srcVal rs1 L).toNat ∧
        WP code P (pos + 1) is K L (applyW m ((srcVal rs1 L).toNat, 8, srcVal rs2 L)) o)) := by rw [WP]
theorem WP_br {op r1 r2 off} : WP code P pos (.br op r1 r2 off :: is) K L m o =
    (SrcOK r1 (keysG L) ∧ SrcOK r2 (keysG L) ∧ BrOK pos off ∧
      (if guardB op.bop (srcVal r1 L) (srcVal r2 L) then Reaches code ⟨pcOf (brT pos off), L, m, o⟩ P
      else WP code P (pos + 1) is K L m o)) := by rw [WP]
theorem WP_jal0 {off} : WP code P pos (.jal 0 off :: is) K L m o =
    (JOK pos off ∧ Reaches code ⟨pcOf (jT pos off), L, m, o⟩ P) := by rw [WP]; rfl
theorem WP_jal1 {off} : WP code P pos (.jal 1 off :: is) K L m o =
    (if isLib pos off then
      SrcOK 10 (keysG L) ∧ SrcOK 11 (keysG L) ∧ 12 ∈ keysG L ∧ 13 ∈ keysG L ∧
      (match libRes (libAddr pos off) (srcVal 10 L) (srcVal 11 L) with
        | some r => WP code P (pos + 1) is K ((10, r) :: eraseAll clobbered L) m o
        | none => False)
    else JOK pos off ∧ Reaches code ⟨pcOf (jT pos off), gset L 1 (pcOf (pos + 1)), m, o⟩ P) := by rw [WP]; rfl
theorem WP_jalr {rs} : WP code P pos (.jalr rs :: is) K L m o =
    (SrcOK rs (keysG L) ∧ (srcVal rs L).toNat % 4 = 0 ∧ Reaches code ⟨srcVal rs L, L, m, o⟩ P) := by rw [WP]

end WPEq

/-! ## Registers as sources -/

theorem mem_keysG_lookup {n : Nat} : ∀ {L : GRegs}, n ∈ keysG L → ∃ v, lookupG n L = some v
  | [], h => by simp [keysG] at h
  | (k, w) :: L, h => by
    simp only [keysG, List.mem_cons] at h
    simp only [lookupG]
    by_cases hk : k = n
    · exact ⟨w, by simp [hk]⟩
    · rw [if_neg hk]
      rcases h with h | h
      · exact absurd h.symm hk
      · exact mem_keysG_lookup h

theorem has_of_src {L : GRegs} {n : Nat} (h : SrcOK n (keysG L)) : Has L n (srcVal n L) := by
  obtain ⟨h31, h0 | hk⟩ := h
  · subst h0; exact Has.zero _
  · by_cases h0 : n = 0
    · subst h0; exact Has.zero _
    · obtain ⟨v, hv⟩ := mem_keysG_lookup hk
      refine ⟨h31, .inr ⟨h0, ?_⟩⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [srcVal, hv]

@[simp] theorem keysG_gset (L : GRegs) (rd : Nat) (v : BitVec 64) (n : Nat) :
    n ∈ keysG (gset L rd v) ↔ n = rd ∨ n ∈ keysG L := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := mem_keysG_lookup h
    rw [lookupG_set] at hw
    by_cases hn : n = rd
    · exact .inl hn
    · rw [if_neg hn] at hw; exact .inr (mem_keysG_of_lookup hw)
  · rintro (h | h)
    · exact mem_keysG_of_lookup (v := v) (by rw [lookupG_set, if_pos h])
    · by_cases hn : n = rd
      · exact mem_keysG_of_lookup (v := v) (by rw [lookupG_set, if_pos hn])
      · obtain ⟨w, hw⟩ := mem_keysG_lookup h
        exact mem_keysG_of_lookup (v := w) (by rw [lookupG_set, if_neg hn, hw])

@[simp] theorem srcOK_gset (L : GRegs) (rd : Nat) (v : BitVec 64) (n : Nat) :
    SrcOK n (keysG (gset L rd v)) ↔ n ≤ 31 ∧ (n = 0 ∨ n = rd ∨ n ∈ keysG L) := by
  simp only [SrcOK, keysG_gset]

@[simp] theorem srcVal_gset (L : GRegs) (rd : Nat) (v : BitVec 64) (n : Nat) :
    srcVal n (gset L rd v) = if n = 0 then 0 else if n = rd then v else srcVal n L := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [srcVal, lookupG_set, Nat.add_one_ne_zero, if_false]
    split <;> rfl

@[simp] theorem srcVal_zero (L : GRegs) : srcVal 0 L = 0 := rfl

theorem srcVal_of_has {L : GRegs} {n : Nat} {v : BitVec 64} (h : Has L n v) : srcVal n L = v :=
  h.src.2

theorem srcOK_of_has {L : GRegs} {n : Nat} {v : BitVec 64} (h : Has L n v) : SrcOK n (keysG L) :=
  h.src.1

/-! ## Soundness -/

theorem lt_of_seg_head {code : List Ins} {pos : Nat} {i : Ins} (h : code[pos]? = some i) :
    pos < code.length := by
  rcases Nat.lt_or_ge pos code.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem pcOf_toNat_of_lt {code : List Ins} (hfit : Fits code) {k : Nat} (hk : k < code.length) :
    (pcOf k).toNat = codeBase + 4 * k := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  unfold Fits at hfit
  exact pcOf_toNat (by omega)

theorem brT_pc {code : List Ins} (hfit : Fits code) {pos : Nat} (hk : pos < code.length)
    {off : BitVec 13} (h : BrOK pos off) :
    pcOf pos + sign_extend (m := 64) (evenB off) = pcOf (brT pos off) := by
  obtain ⟨h4, h0, hp⟩ := h
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  unfold Fits at hfit
  unfold PosOK at hp
  have he : off.toNat % 2 = 0 := by
    have hlt := off.isLt
    rcases (show off.toInt = off.toNat ∨ off.toInt = (off.toNat : Int) - 2 ^ 13 from by
      simp only [BitVec.toInt]; split <;> simp) with h | h <;> omega
  rw [evenB_self _ he, add_sext, pcOf_toNat_of_lt hfit hk, pcOf_eq_ofInt]
  congr 1
  have hb' : ((brT pos off : Nat) : Int) = pos + off.toInt / 4 := by
    unfold brT; exact Int.toNat_of_nonneg h0
  omega

theorem jT_pc {code : List Ins} (hfit : Fits code) {pos : Nat} (hk : pos < code.length)
    {off : BitVec 21} (h : JOK pos off) :
    pcOf pos + sign_extend (m := 64) (evenJ off) = pcOf (jT pos off) := by
  obtain ⟨h4, h0, hp⟩ := h
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  unfold Fits at hfit
  unfold PosOK at hp
  have he : off.toNat % 2 = 0 := by
    have hlt := off.isLt
    rcases (show off.toInt = off.toNat ∨ off.toInt = (off.toNat : Int) - 2 ^ 21 from by
      simp only [BitVec.toInt]; split <;> simp) with h | h <;> omega
  rw [evenJ_self _ he, add_sext, pcOf_toNat_of_lt hfit hk, pcOf_eq_ofInt]
  congr 1
  have hb' : ((jT pos off : Nat) : Int) = pos + off.toInt / 4 := by
    unfold jT; exact Int.toNat_of_nonneg h0
  omega

theorem pcOf_aligned {k : Nat} (hk : PosOK k) : (pcOf k).toNat % 4 = 0 := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  unfold PosOK at hk
  rw [pcOf_toNat (by omega)]; omega

theorem pcOf_not_lib {k : Nat} (hk : PosOK k) :
    ¬ ((pcOf k).toNat = mulPC ∨ (pcOf k).toNat = divPC ∨ (pcOf k).toNat = modPC) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
  unfold PosOK at hk
  rw [pcOf_toNat (by omega)]; omega

theorem lib_pc {code : List Ins} (hfit : Fits code) {pos : Nat} (hk : pos < code.length)
    {off : BitVec 21} (h : isLib pos off = true) :
    pcOf pos + sign_extend (m := 64) (evenJ off) = BitVec.ofNat 64 (libAddr pos off) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
  unfold Fits at hfit
  simp only [isLib, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨he, hl⟩ := h
  rw [evenJ_self _ he, add_sext, pcOf_toNat_of_lt hfit hk]
  unfold libAddr at hl ⊢
  rw [← BitVec.ofInt_natCast]
  congr 1
  omega

theorem lib_mem {pos : Nat} {off : BitVec 21} (h : isLib pos off = true) :
    (BitVec.ofNat 64 (libAddr pos off)).toNat = mulPC ∨
      (BitVec.ofNat 64 (libAddr pos off)).toNat = divPC ∨
      (BitVec.ofNat 64 (libAddr pos off)).toNat = modPC := by
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
  simp only [isLib, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨-, hl⟩ := h
  rw [BitVec.toNat_ofNat]
  omega

theorem lib_aligned {pos : Nat} {off : BitVec 21} (h : isLib pos off = true) :
    (BitVec.ofNat 64 (libAddr pos off)).toNat % 4 = 0 := by
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
  have := lib_mem h
  omega

/-- **Soundness of the VCG.** -/
theorem WP_sound {code : List Ins} {P : AM → Prop} (hfit : Fits code) :
    ∀ (is : List Ins) (pos : Nat) (K : GRegs → Mem → Array String → Prop) (L : GRegs) (m : Mem)
      (o : Array String), Seg code pos is →
      (∀ L' m' o', K L' m' o' → Reaches code ⟨pcOf (pos + is.length), L', m', o'⟩ P) →
      WP code P pos is K L m o → Reaches code ⟨pcOf pos, L, m, o⟩ P
  | [], pos, K, L, m, o, _, hK, h => by simpa using hK L m o h
  | i :: is, pos, K, L, m, o, hseg, hK, h => by
    have hk := hseg.head
    have hlt := lt_of_seg_head hk
    have hK' : ∀ L' m' o', K L' m' o' → Reaches code ⟨pcOf (pos + 1 + is.length), L', m', o'⟩ P := by
      intro L' m' o' h'; have := hK L' m' o' h'
      simpa [Nat.add_assoc, Nat.add_comm 1] using this
    have ih := WP_sound (P := P) hfit is (pos + 1) K
    cases i with
    | addi rd rs imm =>
      obtain ⟨hrd, hs, hw⟩ := h
      exact ex_step (step_addi hfit hk rfl hrd (has_of_src hs)) (ih _ _ _ hseg.tail hK' hw)
    | ori rd rs imm =>
      obtain ⟨hrd, hs, hw⟩ := h
      exact ex_step (step_ori hfit hk rfl hrd (has_of_src hs)) (ih _ _ _ hseg.tail hK' hw)
    | slli rd rs sh =>
      obtain ⟨hrd, hs, hw⟩ := h
      exact ex_step (step_slli hfit hk rfl hrd (has_of_src hs)) (ih _ _ _ hseg.tail hK' hw)
    | add rd r1 r2 =>
      obtain ⟨hrd, h1, h2, hw⟩ := h
      exact ex_step (step_add hfit hk rfl hrd (has_of_src h1) (has_of_src h2))
        (ih _ _ _ hseg.tail hK' hw)
    | sub rd r1 r2 =>
      obtain ⟨hrd, h1, h2, hw⟩ := h
      exact ex_step (step_sub hfit hk rfl hrd (has_of_src h1) (has_of_src h2))
        (ih _ _ _ hseg.tail hK' hw)
    | ld rd rs =>
      obtain ⟨hrd, hs, ha, hw⟩ := h
      exact ex_step (step_ld hfit hk rfl hrd (has_of_src hs) ha) (ih _ _ _ hseg.tail hK' hw)
    | sd rs2 rs1 =>
      obtain ⟨h1, h2, hw⟩ := h
      split at hw
      · next ht =>
        obtain ⟨hv, hw⟩ := hw
        have e := step_htif hfit hk (A := ⟨pcOf pos, L, m, o⟩) rfl (has_of_src h1) (has_of_src h2) ht
        rw [hv, htifOut_putc] at e
        simp only [pcOf_succ] at e
        exact ex_step e (ih _ _ _ hseg.tail hK' hw)
      · obtain ⟨hs, hw⟩ := hw
        exact ex_step (step_sd hfit hk rfl (has_of_src h1) (has_of_src h2) hs)
          (ih _ _ _ hseg.tail hK' hw)
    | br op r1 r2 off =>
      obtain ⟨h1, h2, hb, hw⟩ := h
      have htgt := brT_pc hfit hlt hb
      have e := step_br hfit hk (A := ⟨pcOf pos, L, m, o⟩) rfl (has_of_src h1) (has_of_src h2)
        (by rw [htgt]; exact pcOf_aligned hb.2.2)
      rw [htgt] at e
      split at hw
      · next hg => rw [if_pos hg] at e; exact ex_step e hw
      · next hg => rw [if_neg hg] at e; exact ex_step e (ih _ _ _ hseg.tail hK' hw)
    | jal rd off =>
      simp only [WP] at h
      split at h
      · next h0 =>
        subst h0
        obtain ⟨hj, hw⟩ := h
        have htgt := jT_pc hfit hlt hj
        have e := step_j hfit hk (A := ⟨pcOf pos, L, m, o⟩) rfl (by rw [htgt]; exact pcOf_aligned hj.2.2)
        rw [htgt] at e
        exact ex_step e hw
      · split at h
        · next h1 =>
          subst h1
          split at h
          · next hl =>
            obtain ⟨h10, h11, h12, h13, hw⟩ := h
            split at hw
            · next r hr =>
              have htgt := lib_pc hfit hlt hl
              have e := step_lib hfit hk (A := ⟨pcOf pos, L, m, o⟩) rfl
                (by rw [htgt]; exact lib_aligned hl) (by rw [htgt]; exact lib_mem hl)
              rw [htgt] at e
              obtain ⟨x, hx⟩ := mem_keysG_lookup (show 10 ∈ keysG L from by
                rcases h10.2 with h | h
                · cases h
                · exact h)
              obtain ⟨y, hy⟩ := mem_keysG_lookup (show 11 ∈ keysG L from by
                rcases h11.2 with h | h
                · cases h
                · exact h)
              have ex : srcVal 10 L = x := by simp [srcVal, hx]
              have ey : srcVal 11 L = y := by simp [srcVal, hy]
              rw [ex, ey] at hr
              have hlt' : (BitVec.ofNat 64 (libAddr pos off)).toNat = libAddr pos off := by
                have hl2 := hl
                simp only [isLib, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hl2
                have hm : mulPC = 0x80004640 := rfl
                have hd : divPC = 0x800046a4 := rfl
                have hmo : modPC = 0x80004728 := rfl
                rw [BitVec.toNat_ofNat]; omega
              rw [hlt'] at e
              rw [libCall_eq _ ⟨pcOf pos, L, m, o⟩ hx hy h12 h13 hr] at e
              simp only [pcOf_succ] at e
              exact ex_step e (ih _ _ _ hseg.tail hK' hw)
            · exact hw.elim
          · next hl =>
            obtain ⟨hj, hw⟩ := h
            have htgt := jT_pc hfit hlt hj
            have e := step_call hfit hk (A := ⟨pcOf pos, L, m, o⟩) rfl
              (by rw [htgt]; exact pcOf_aligned hj.2.2) (by rw [htgt]; exact pcOf_not_lib hj.2.2)
            rw [htgt] at e
            exact ex_step e hw
        · exact h.elim
    | jalr rs =>
      obtain ⟨hs, hal, hw⟩ := h
      exact ex_step (step_jalr hfit hk rfl (has_of_src hs) hal) hw

/-- `WP` of a concatenation. -/
theorem WP_append (code : List Ins) (P : AM → Prop) :
    ∀ (s t : List Ins) (pos : Nat) (K : GRegs → Mem → Array String → Prop) (L : GRegs) (m : Mem)
      (o : Array String),
      WP code P pos (s ++ t) K L m o = WP code P pos s (WP code P (pos + s.length) t K) L m o
  | [], t, pos, K, L, m, o => by simp [WP]
  | i :: s, t, pos, K, L, m, o => by
    have ih := WP_append code P s t (pos + 1) K
    have e : pos + (i :: s).length = pos + 1 + s.length := by simp; omega
    rw [e]
    cases i <;> simp only [List.cons_append, WP, ih]

/-- Monotonicity of `WP` in the continuation. -/
theorem WP_mono {code : List Ins} {P : AM → Prop} :
    ∀ (is : List Ins) (pos : Nat) (K K' : GRegs → Mem → Array String → Prop) (L : GRegs) (m : Mem)
      (o : Array String), (∀ L m o, K L m o → K' L m o) →
      WP code P pos is K L m o → WP code P pos is K' L m o
  | [], _, K, K', L, m, o, hK, h => hK L m o h
  | i :: is, pos, K, K', L, m, o, hK, h => by
    have ih := WP_mono (code := code) (P := P) is (pos + 1) K K'
    cases i with
    | addi => exact ⟨h.1, h.2.1, ih _ _ _ hK h.2.2⟩
    | ori => exact ⟨h.1, h.2.1, ih _ _ _ hK h.2.2⟩
    | slli => exact ⟨h.1, h.2.1, ih _ _ _ hK h.2.2⟩
    | add => exact ⟨h.1, h.2.1, h.2.2.1, ih _ _ _ hK h.2.2.2⟩
    | sub => exact ⟨h.1, h.2.1, h.2.2.1, ih _ _ _ hK h.2.2.2⟩
    | ld => exact ⟨h.1, h.2.1, h.2.2.1, ih _ _ _ hK h.2.2.2⟩
    | sd rs2 rs1 =>
      obtain ⟨h1, h2, hw⟩ := h
      refine ⟨h1, h2, ?_⟩
      split
      · next ht => rw [if_pos ht] at hw; exact ⟨hw.1, ih _ _ _ hK hw.2⟩
      · next ht => rw [if_neg ht] at hw; exact ⟨hw.1, ih _ _ _ hK hw.2⟩
    | br =>
      obtain ⟨h1, h2, hb, hw⟩ := h
      refine ⟨h1, h2, hb, ?_⟩
      split
      · next hg => rw [if_pos hg] at hw; exact hw
      · next hg => rw [if_neg hg] at hw; exact ih _ _ _ hK hw
    | jal rd off =>
      simp only [WP] at h ⊢
      split
      · next h0 => rw [if_pos h0] at h; exact h
      · next h0 =>
        rw [if_neg h0] at h
        split
        · next h1 =>
          rw [if_pos h1] at h
          split
          · next hl =>
            rw [if_pos hl] at h
            obtain ⟨h10, h11, h12, h13, hw⟩ := h
            refine ⟨h10, h11, h12, h13, ?_⟩
            split
            · next r hr => rw [hr] at hw; exact ih _ _ _ hK hw
            · next hr => rw [hr] at hw; exact hw
          · next hl => rw [if_neg hl] at h; exact h
        · next h1 => rw [if_neg h1] at h; exact h
    | jalr => exact h

/-! ## Constants -/

theorem li_value (n : BitVec 64) :
    (((((((sign_extend (chunk n 0) : BitVec 64)) <<< 11 ||| sign_extend (chunk n 1)) <<< 11 |||
      sign_extend (chunk n 2)) <<< 11 ||| sign_extend (chunk n 3)) <<< 11 ||| sign_extend (chunk n 4)) <<< 11 |||
      sign_extend (chunk n 5)) = n := by
  have hN := n.isLt
  have hc0 : (chunk n 0).toNat = n.toNat / 2 ^ 55 := by simp [chunk]; omega
  have hx0 : ((sign_extend (chunk n 0) : BitVec 64)).toNat = n.toNat / 2 ^ 44 / 2 ^ 11 := by
    rw [sext12_small _ (by rw [hc0]; omega), hc0, Nat.div_div_eq_div_mul]
  generalize (sign_extend (chunk n 0) : BitVec 64) = x0 at hx0
  have h1 := li_stage x0 n.toNat 44 hN hx0
  rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 44 % 2048) = chunk n 1 from rfl] at h1
  generalize (x0 <<< 11) ||| (sign_extend (chunk n 1) : BitVec 64) = x1 at h1
  have h2 := li_stage x1 n.toNat 33 hN (by rw [h1, Nat.div_div_eq_div_mul])
  rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 33 % 2048) = chunk n 2 from rfl] at h2
  generalize (x1 <<< 11) ||| (sign_extend (chunk n 2) : BitVec 64) = x2 at h2
  have h3 := li_stage x2 n.toNat 22 hN (by rw [h2, Nat.div_div_eq_div_mul])
  rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 22 % 2048) = chunk n 3 from rfl] at h3
  generalize (x2 <<< 11) ||| (sign_extend (chunk n 3) : BitVec 64) = x3 at h3
  have h4 := li_stage x3 n.toNat 11 hN (by rw [h3, Nat.div_div_eq_div_mul])
  rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 11 % 2048) = chunk n 4 from rfl] at h4
  generalize (x3 <<< 11) ||| (sign_extend (chunk n 4) : BitVec 64) = x4 at h4
  have h5 := li_stage x4 n.toNat 0 hN (by rw [h4]; simp)
  rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 0 % 2048) = chunk n 5 from rfl] at h5
  apply BitVec.eq_of_toNat_eq; rw [h5]; simp

/-- `li rd n` loads `n`. -/
theorem WP_li {code : List Ins} {P : AM → Prop} {pos rd : Nat} {n : BitVec 64}
    {K : GRegs → Mem → Array String → Prop} {L : GRegs} {m : Mem} {o : Array String}
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hK : K (gset L rd n) m o) :
    WP code P pos (li rd n) K L m o := by
  have h0 : rd ≠ 0 := by omega
  unfold li
  split
  · next hs =>
    simp only [WP, srcVal_gset, srcVal_zero, SrcOK]
    refine ⟨hrd, ⟨by omega, .inl trivial⟩, ?_⟩
    rw [sext12_ofInt _ hs.2 hs.1, BitVec.ofInt_toInt]; simpa using hK
  · next hs =>
    simp [WP, List.range, List.range.loop, h0, hrd, gset_gset, SrcOK, li_value, hK]

/-- `li rd n` followed by `is`. -/
theorem WP_li_append {code : List Ins} {P : AM → Prop} {pos rd : Nat} {n : BitVec 64} {is : List Ins}
    {K : GRegs → Mem → Array String → Prop} {L : GRegs} {m : Mem} {o : Array String}
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (h : WP code P (pos + (li rd n).length) is K (gset L rd n) m o) :
    WP code P pos (li rd n ++ is) K L m o := by
  rw [WP_append]; exact WP_li hrd h

/-- `li rd n` followed by `is`, as an equivalence. -/
theorem WP_li_iff {code : List Ins} {P : AM → Prop} {pos rd : Nat} {n : BitVec 64} {is : List Ins}
    {K : GRegs → Mem → Array String → Prop} {L : GRegs} {m : Mem} {o : Array String}
    (hrd : 1 ≤ rd ∧ rd ≤ 31) :
    WP code P pos (li rd n ++ is) K L m o ↔
      WP code P (pos + (li rd n).length) is K (gset L rd n) m o := by
  have h0 : rd ≠ 0 := by omega
  rw [WP_append]
  unfold li
  split
  · next hs =>
    simp only [WP, srcVal_gset, srcVal_zero, SrcOK]
    rw [sext12_ofInt _ hs.2 hs.1, BitVec.ofInt_toInt]
    simp [hrd]
  · next hs =>
    simp [WP, List.range, List.range.loop, h0, hrd, gset_gset, SrcOK, li_value]

theorem WP_li_end {code : List Ins} {P : AM → Prop} {pos rd : Nat} {n : BitVec 64}
    {K : GRegs → Mem → Array String → Prop} {L : GRegs} {m : Mem} {o : Array String}
    (hrd : 1 ≤ rd ∧ rd ≤ 31) :
    WP code P pos (li rd n) K L m o ↔ K (gset L rd n) m o := by
  have := WP_li_iff (code := code) (P := P) (pos := pos) (is := []) (K := K) (L := L) (m := m) (o := o)
    (n := n) hrd
  rw [List.append_nil] at this
  rw [this, WP_nil]

theorem li_length_small {rd : Nat} {n : BitVec 64} (h : n.toInt < 2048 ∧ -2048 ≤ n.toInt) :
    (li rd n).length = 1 := by simp [li, h]

theorem li_length_big {rd : Nat} {n : BitVec 64} (h : ¬ (n.toInt < 2048 ∧ -2048 ≤ n.toInt)) :
    (li rd n).length = 11 := by simp [li, h, List.range, List.range.loop]

theorem libc_off_facts {pos tgt : Nat} (ht : tgt = mulPC ∨ tgt = divPC ∨ tgt = modPC)
    (hp : PosOK (pos + 2)) :
    isLib (pos + 2) (BitVec.ofInt 21 ((tgt : Int) - (codeBase + 4 * (pos + 2)))) = true ∧
      libAddr (pos + 2) (BitVec.ofInt 21 ((tgt : Int) - (codeBase + 4 * (pos + 2)))) = tgt := by
  have hb : codeBase = 0x80004800 := rfl
  have htt : tohostAddr = 0x8001ad00 := rfl
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
  unfold PosOK at hp
  have hj : (BitVec.ofInt 21 ((tgt : Int) - (codeBase + 4 * (pos + 2)))).toInt
      = (tgt : Int) - (codeBase + 4 * (pos + 2)) := by
    rw [BitVec.toInt_ofInt]
    apply Int.bmod_eq_of_le <;> simp <;> omega
  have he : (BitVec.ofInt 21 ((tgt : Int) - (codeBase + 4 * (pos + 2)))).toNat % 2 = 0 := by
    rw [BitVec.toNat_ofInt]; omega
  have hl : libAddr (pos + 2) (BitVec.ofInt 21 ((tgt : Int) - (codeBase + 4 * (pos + 2)))) = tgt := by
    unfold libAddr; rw [hj]; omega
  refine ⟨?_, hl⟩
  simp only [isLib, hl, he, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, beq_iff_eq]
  omega

/-- A libgcc call sequence followed by `is`. -/
theorem WP_libc_iff {code : List Ins} {P : AM → Prop} {pos tgt : Nat} {is : List Ins}
    {K : GRegs → Mem → Array String → Prop} {L : GRegs} {m : Mem} {o : Array String}
    (ht : tgt = mulPC ∨ tgt = divPC ∨ tgt = modPC) (hp : PosOK (pos + 2)) :
    WP code P pos (libc pos tgt ++ is) K L m o ↔
      SrcOK 10 (keysG L) ∧ SrcOK 11 (keysG L) ∧
      (match libRes tgt (srcVal 10 L) (srcVal 11 L) with
        | some r => WP code P (pos + 3) is K ((10, r) :: eraseAll clobbered (gset (gset L 12 0) 13 0)) m o
        | none => False) := by
  obtain ⟨hl, ha⟩ := libc_off_facts ht hp
  have hz : (0 : BitVec 64) + sign_extend (0 : BitVec 12) = 0 := by decide
  simp only [libc, List.cons_append, List.nil_append, WP, srcVal_zero, hz, if_neg (show (1 : Nat) ≠ 0 by decide),
    if_true, hl, ha, srcVal_gset, show (10 : Nat) ≠ 0 by decide, show (11 : Nat) ≠ 0 by decide,
    show (10 : Nat) ≠ 12 by decide, show (10 : Nat) ≠ 13 by decide, show (11 : Nat) ≠ 12 by decide,
    show (11 : Nat) ≠ 13 by decide, if_false, SrcOK, keysG_gset, Nat.add_assoc, ra]
  simp only [show (1 : Nat) + 1 + 1 = 3 by rfl, show (0 : Nat) ≤ 31 by decide, show (12 : Nat) ≤ 31 by decide,
    show (13 : Nat) ≤ 31 by decide, show (1 : Nat) ≤ 12 by decide, show (1 : Nat) ≤ 13 by decide]
  simp

theorem isLib_of_JOK {pos : Nat} {off : BitVec 21} (h : JOK pos off) : isLib pos off = false := by
  obtain ⟨h4, h0, hp⟩ := h
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
  unfold PosOK at hp
  simp only [isLib, libAddr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, Bool.or_eq_false_iff, ne_eq]
  right
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

/-! ## Branch offsets -/

/-- Byte offset of a branch from instruction `src` to instruction `dst`. -/
def bOff (src dst : Nat) : BitVec 13 := BitVec.ofInt 13 (4 * ((dst : Int) - src))

theorem bOff_ok {src dst : Nat} (hd : PosOK dst) (h1 : src ≤ dst + 1000) (h2 : dst ≤ src + 1000) :
    brT src (bOff src dst) = dst ∧ BrOK src (bOff src dst) := by
  have hi : (bOff src dst).toInt = 4 * ((dst : Int) - src) := by
    unfold bOff; rw [BitVec.toInt_ofInt]
    apply Int.bmod_eq_of_le <;> simp <;> omega
  have hb : brT src (bOff src dst) = dst := by
    unfold brT; rw [hi]; omega
  refine ⟨hb, ?_, ?_, ?_⟩
  · rw [hi]; omega
  · rw [hi]; omega
  · rw [hb]; exact hd

theorem jOff_ok {src dst : Nat} (hs : PosOK src) (hd : PosOK dst) :
    jT src (jOff src dst) = dst ∧ JOK src (jOff src dst) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  unfold PosOK at hs hd
  have hi : (jOff src dst).toInt = 4 * ((dst : Int) - src) := by
    unfold jOff; rw [BitVec.toInt_ofInt]
    apply Int.bmod_eq_of_le <;> simp <;> omega
  have hj : jT src (jOff src dst) = dst := by
    unfold jT; rw [hi]; omega
  refine ⟨hj, ?_, ?_, ?_⟩
  · rw [hi]; omega
  · rw [hi]; omega
  · rw [hj]; unfold PosOK; omega

instance (pos : Nat) (off : BitVec 13) : Decidable (BrOK pos off) := by
  unfold BrOK; infer_instance

instance (pos : Nat) (off : BitVec 21) : Decidable (JOK pos off) := by
  unfold JOK; infer_instance

theorem brT_bOff_of {s d : Nat} (hd : PosOK d) (h1 : s ≤ d + 1000) (h2 : d ≤ s + 1000) :
    brT s (bOff s d) = d := (bOff_ok hd h1 h2).1

theorem BrOK_bOff_of {s d : Nat} (hd : PosOK d) (h1 : s ≤ d + 1000) (h2 : d ≤ s + 1000) :
    BrOK s (bOff s d) ↔ True := iff_true_intro (bOff_ok hd h1 h2).2

theorem jT_jOff_of {s d : Nat} (hs : PosOK s) (hd : PosOK d) : jT s (jOff s d) = d :=
  (jOff_ok hs hd).1

theorem JOK_jOff_of {s d : Nat} (hs : PosOK s) (hd : PosOK d) : JOK s (jOff s d) ↔ True :=
  iff_true_intro (jOff_ok hs hd).2

theorem brT_bOff_gen {s s' d : Nat} (he : s' = s) (hd : PosOK d) (h1 : s ≤ d + 1000)
    (h2 : d ≤ s + 1000) : brT s (bOff s' d) = d := by subst he; exact (bOff_ok hd h1 h2).1

theorem BrOK_bOff_gen {s s' d : Nat} (he : s' = s) (hd : PosOK d) (h1 : s ≤ d + 1000)
    (h2 : d ≤ s + 1000) : BrOK s (bOff s' d) ↔ True := by subst he; exact iff_true_intro (bOff_ok hd h1 h2).2

theorem jT_jOff_gen {s s' d : Nat} (he : s' = s) (hs : PosOK s) (hd : PosOK d) : jT s (jOff s' d) = d := by
  subst he; exact (jOff_ok hs hd).1

theorem JOK_jOff_gen {s s' d : Nat} (he : s' = s) (hs : PosOK s) (hd : PosOK d) :
    JOK s (jOff s' d) ↔ True := by subst he; exact iff_true_intro (jOff_ok hs hd).2

theorem isLib_jOff_gen {s s' d : Nat} (he : s' = s) (hs : PosOK s) (hd : PosOK d) :
    isLib s (jOff s' d) = false := by subst he; exact isLib_of_JOK (jOff_ok hs hd).2

theorem sext_ofInt12 (k : Int) (h : -2048 ≤ k ∧ k < 2048) :
    (sign_extend (BitVec.ofInt 12 k) : BitVec 64) = BitVec.ofInt 64 k := sext12_ofInt k h.1 h.2

/-! ## Branch guards -/

@[simp] theorem guard_eq (v w : BitVec 64) : guardB BrOp.eq.bop v w = decide (v = w) := by
  simp only [guardB, BrOp.bop]; by_cases h : v = w <;> simp [h]

@[simp] theorem guard_ne (v w : BitVec 64) : guardB BrOp.ne.bop v w = decide (v ≠ w) := by
  simp only [guardB, BrOp.bop]; by_cases h : v = w <;> simp [h]

@[simp] theorem guard_lt (v w : BitVec 64) : guardB BrOp.lt.bop v w = decide (v.toInt < w.toInt) := by
  simp [guardB, BrOp.bop, zopz0zI_s]

@[simp] theorem guard_ge (v w : BitVec 64) : guardB BrOp.ge.bop v w = decide (v.toInt ≥ w.toInt) := by
  simp [guardB, BrOp.bop, zopz0zKzJ_s]

end Vsa.Compiler

import Vsa.Compiler.Run

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim

theorem gset_gset (L : GRegs) (rd : Nat) (a b : BitVec 64) : gset (gset L rd a) rd b = gset L rd b := by
  simp only [gset, eraseG, if_true]
  congr 1
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    by_cases h : m = rd <;> simp [eraseG, h, ih]

theorem sext12_small (c : BitVec 12) (h : c.toNat < 2048) :
    (sign_extend c : BitVec 64).toNat = c.toNat := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend, BitVec.toNat_ofInt]
  rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  simp; omega

theorem sext12_ofInt (t : Int) (h1 : -2048 ≤ t) (h2 : t < 2048) :
    (sign_extend (BitVec.ofInt 12 t) : BitVec 64) = BitVec.ofInt 64 t := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend]
  congr 1
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le <;> simp <;> omega

theorem li_stage (x : BitVec 64) (N s : Nat) (hN : N < 2 ^ 64)
    (hx : x.toNat = N / 2 ^ s / 2 ^ 11) :
    ((x <<< 11) ||| (sign_extend (BitVec.ofNat 12 (N / 2 ^ s % 2048)) : BitVec 64)).toNat
      = N / 2 ^ s := by
  have hc : (BitVec.ofNat 12 (N / 2 ^ s % 2048)).toNat = N / 2 ^ s % 2048 := by
    simp; omega
  have ht : N / 2 ^ s < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hN
  rw [BitVec.toNat_or, sext12_small _ (by rw [hc]; omega), hc, BitVec.toNat_shiftLeft, hx,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (by omega : N / 2 ^ s % 2048 < 2 ^ 11)]
  omega

theorem Seg.sub {code : List Ins} {pos : Nat} {s : List Ins} (h : Seg code pos s) (p q : Nat) :
    Seg code (pos + p) ((s.drop p).take q) := by
  intro j hj
  simp only [List.length_take, List.length_drop] at hj
  rw [Nat.add_assoc, h (p + j) (by omega)]
  simp [List.getElem?_take, hj]

section
variable {code : List Ins} {pos : Nat} {A : AM}

theorem run_stage (hfit : Fits code) {rd : Nat} {c : BitVec 12} {x : BitVec 64}
    (hseg : Seg code pos [.slli rd rd 11#6, .ori rd rd c]) (hA : A.pc = pcOf pos)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hx : Has A.regs rd x) :
    Star code A ⟨pcOf (pos + 2), gset A.regs rd ((x <<< 11) ||| (sign_extend c : BitVec 64)),
      A.mem, A.out⟩ := by
  refine Star.step (step_slli hfit hseg.head hA hrd hx) (Star.single ?_)
  rw [step_ori hfit hseg.tail.head rfl hrd (Has.set_self _ _ hrd.1 hrd.2), gset_gset]
  rfl

theorem run_li (hfit : Fits code) {rd : Nat} {n : BitVec 64} (hseg : Seg code pos (li rd n))
    (hA : A.pc = pcOf pos) (hrd : 1 ≤ rd ∧ rd ≤ 31) :
    Star code A ⟨pcOf (pos + (li rd n).length), gset A.regs rd n, A.mem, A.out⟩ := by
  by_cases hs : n.toInt < 2048 ∧ -2048 ≤ n.toInt
  · have hl : li rd n = [.addi rd 0 (BitVec.ofInt 12 n.toInt)] := by simp [li, hs]
    rw [hl] at hseg ⊢
    apply Star.single
    rw [step_addi hfit hseg.head hA hrd (Has.zero _), sext12_ofInt _ hs.2 hs.1,
      BitVec.ofInt_toInt]
    simp
  · have hl : li rd n = [.addi rd 0 (chunk n 0), .slli rd rd 11#6, .ori rd rd (chunk n 1),
        .slli rd rd 11#6, .ori rd rd (chunk n 2), .slli rd rd 11#6, .ori rd rd (chunk n 3),
        .slli rd rd 11#6, .ori rd rd (chunk n 4), .slli rd rd 11#6, .ori rd rd (chunk n 5)] := by
      simp [li, hs, List.range, List.range.loop]
    rw [hl] at hseg ⊢
    have hN := n.isLt
    have hc0 : (chunk n 0).toNat = n.toNat / 2 ^ 55 := by simp [chunk]; omega
    have hx0 : ((0 : BitVec 64) + (sign_extend (chunk n 0) : BitVec 64)).toNat
        = n.toNat / 2 ^ 44 / 2 ^ 11 := by
      rw [show (0 : BitVec 64) + (sign_extend (chunk n 0) : BitVec 64)
        = (sign_extend (chunk n 0) : BitVec 64) by simp]
      rw [sext12_small _ (by rw [hc0]; omega), hc0, Nat.div_div_eq_div_mul]
    generalize hy0 : (0 : BitVec 64) + (sign_extend (chunk n 0) : BitVec 64) = x0 at hx0
    have h1 := li_stage x0 n.toNat 44 hN hx0
    rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 44 % 2048) = chunk n 1 from rfl] at h1
    generalize hy1 : (x0 <<< 11) ||| (sign_extend (chunk n 1) : BitVec 64) = x1 at h1
    have h2 := li_stage x1 n.toNat 33 hN (by rw [h1, Nat.div_div_eq_div_mul])
    rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 33 % 2048) = chunk n 2 from rfl] at h2
    generalize hy2 : (x1 <<< 11) ||| (sign_extend (chunk n 2) : BitVec 64) = x2 at h2
    have h3 := li_stage x2 n.toNat 22 hN (by rw [h2, Nat.div_div_eq_div_mul])
    rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 22 % 2048) = chunk n 3 from rfl] at h3
    generalize hy3 : (x2 <<< 11) ||| (sign_extend (chunk n 3) : BitVec 64) = x3 at h3
    have h4 := li_stage x3 n.toNat 11 hN (by rw [h3, Nat.div_div_eq_div_mul])
    rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 11 % 2048) = chunk n 4 from rfl] at h4
    generalize hy4 : (x3 <<< 11) ||| (sign_extend (chunk n 4) : BitVec 64) = x4 at h4
    have h5 := li_stage x4 n.toNat 0 hN (by rw [h4]; simp)
    rw [show BitVec.ofNat 12 (n.toNat / 2 ^ 0 % 2048) = chunk n 5 from rfl] at h5
    have hx5 : (x4 <<< 11) ||| (sign_extend (chunk n 5) : BitVec 64) = n := by
      apply BitVec.eq_of_toNat_eq; rw [h5]; simp
    have e0 := step_addi hfit hseg.head hA hrd (Has.zero _)
    rw [hy0] at e0
    refine Star.step e0 ?_
    have t1 := run_stage hfit (A := ⟨pcOf (pos + 1), gset A.regs rd x0, A.mem, A.out⟩)
      (by simpa using hseg.sub 1 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hy1] at t1
    have t2 := run_stage hfit (A := ⟨pcOf (pos + 1 + 2), gset A.regs rd x1, A.mem, A.out⟩)
      (by simpa using hseg.sub 3 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hy2] at t2
    have t3 := run_stage hfit (A := ⟨pcOf (pos + 1 + 2 + 2), gset A.regs rd x2, A.mem, A.out⟩)
      (by simpa using hseg.sub 5 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hy3] at t3
    have t4 := run_stage hfit (A := ⟨pcOf (pos + 1 + 2 + 2 + 2), gset A.regs rd x3, A.mem, A.out⟩)
      (by simpa using hseg.sub 7 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hy4] at t4
    have t5 := run_stage hfit (A := ⟨pcOf (pos + 1 + 2 + 2 + 2 + 2), gset A.regs rd x4, A.mem, A.out⟩)
      (by simpa using hseg.sub 9 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hx5] at t5
    have := ((((t1.trans t2).trans t3).trans t4).trans t5)
    simpa using this

end

theorem rd8_write (m : Mem) (a : Nat) (v : BitVec 64) :
    rd8 (applyW m (a, 8, v)) a = [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8,
      v.extractLsb' 24 8, v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8,
      v.extractLsb' 56 8] := by
  have hs : sdData_val v = v := by
    apply BitVec.eq_of_toNat_eq
    simp [sdData_val, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  simp only [rd8, applyW, writeMap8, hs, Std.ExtHashMap.getElem?_insert]
  simp

theorem rdW_write (m : Mem) (a : Nat) (v : BitVec 64) : rdW (applyW m (a, 8, v)) a = v := by
  rw [rdW, rd8_write]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [bytesVal, List.getD_cons_succ, List.getD_cons_zero, sign_extend,
    Sail.BitVec.signExtend]
  rw [BitVec.getLsbD_signExtend]
  simp only [BitVec.append_eq, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨
    (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64) := by omega
  rcases this with h|h|h|h|h|h|h|h <;>
  · simp (disch := omega) only [Nat.add_sub_cancel', decide_true, Bool.true_and, hi, ite_true,
      ite_false, if_pos, if_neg, show i < 8 * 8 from hi, Nat.sub_sub, Nat.zero_add]
    rw [decide_eq_true (by omega), Bool.true_and]

theorem rdW_write_other (m : Mem) (a b : Nat) (v : BitVec 64) (h : a + 8 ≤ b ∨ b + 8 ≤ a) :
    rdW (applyW m (b, 8, v)) a = rdW m a := by
  have hs : sdData_val v = v := by
    apply BitVec.eq_of_toNat_eq
    simp [sdData_val, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  unfold rdW rd8
  simp only [applyW, writeMap8, Std.ExtHashMap.getElem?_insert]
  congr 1
  simp only [List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
  · simp only [beq_iff_eq]
    repeat (rw [if_neg (by omega)])

def libRes (tgt : Nat) (x y : BitVec 64) : Option (BitVec 64) :=
  if tgt = mulPC then some (x * y)
  else if tgt = divPC ∧ y.toInt ≠ 0 then some (BitVec.ofInt 64 (x.toInt.tdiv y.toInt))
  else if tgt = modPC ∧ y.toInt ≠ 0 then some (BitVec.ofInt 64 (x.toInt.tmod y.toInt))
  else none

theorem libCall_eq (tgt : Nat) (A : AM) {x y : BitVec 64} (hx : lookupG 10 A.regs = some x)
    (hy : lookupG 11 A.regs = some y) (h12 : 12 ∈ keysG A.regs) (h13 : 13 ∈ keysG A.regs)
    {r : BitVec 64} (hr : libRes tgt x y = some r) :
    libCall tgt A = some (.run ⟨BitVec.addInt A.pc 4, (10, r) :: eraseAll clobbered A.regs,
      A.mem, A.out⟩) := by
  unfold libCall
  rw [hx, hy]
  simp only
  rw [if_pos ⟨h12, h13⟩]
  unfold libRes at hr
  split at hr
  · cases hr; simp_all
  · split at hr
    · cases hr; simp_all
    · split at hr
      · cases hr; simp_all
      · cases hr

theorem lookupG_eraseAll (ns : List Nat) (n : Nat) (L : GRegs) :
    lookupG n (eraseAll ns L) = if n ∈ ns then none else lookupG n L := by
  induction ns generalizing L with
  | nil => simp [eraseAll]
  | cons m ns ih =>
    simp only [eraseAll, List.foldl_cons] at ih ⊢
    rw [ih, lookupG_eraseG]
    by_cases h1 : n = m <;> by_cases h2 : n ∈ ns <;> simp_all

theorem pcOf_lib (pos tgt : Nat) (hp : PosOK pos) (ht : tgt = mulPC ∨ tgt = divPC ∨ tgt = modPC)
    (o : Int) (ho : o = (tgt : Int) - ((codeBase + 4 * pos : Nat) : Int)) :
    pcOf pos + (sign_extend (evenJ (BitVec.ofInt 21 o)) : BitVec 64) = BitVec.ofNat 64 tgt := by
  subst ho
  have hb : codeBase = 0x80004800 := rfl
  have htt : tohostAddr = 0x8001ad00 := rfl
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
  have hj : (BitVec.ofInt 21 ((tgt : Int) - ((codeBase + 4 * pos : Nat) : Int))).toInt
      = (tgt : Int) - ((codeBase + 4 * pos : Nat) : Int) := by
    rw [BitVec.toInt_ofInt]
    apply Int.bmod_eq_of_le <;> simp <;> omega
  have he : (BitVec.ofInt 21 ((tgt : Int) - ((codeBase + 4 * pos : Nat) : Int))).toNat % 2 = 0 := by
    rw [BitVec.toNat_ofInt]; omega
  rw [evenJ_self _ he, add_sext, pcOf_toNat (by omega), hj, ← BitVec.ofInt_natCast]
  congr 1; omega

theorem run_libc (hfit : Fits code) {pos tgt : Nat} {A : AM} {x y r : BitVec 64}
    (hseg : Seg code pos (libc pos tgt)) (hA : A.pc = pcOf pos) (hp : PosOK (pos + 3))
    (ht : tgt = mulPC ∨ tgt = divPC ∨ tgt = modPC)
    (hx : Has A.regs 10 x) (hy : Has A.regs 11 y) (hr : libRes tgt x y = some r) :
    Star code A ⟨pcOf (pos + 3), (10, r) :: eraseAll clobbered
      (gset (gset A.regs 12 0) 13 0), A.mem, A.out⟩ := by
  have hb : codeBase = 0x80004800 := rfl
  have htt : tohostAddr = 0x8001ad00 := rfl
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
  have hz : (sign_extend (0#12) : BitVec 64) = 0 := by decide
  have e1 : astep code A = some (.run ⟨pcOf (pos + 1), gset A.regs 12 0, A.mem, A.out⟩) := by
    rw [step_addi hfit hseg.head hA (by decide) (Has.zero _) (rd := 12) (imm := 0)]
    have : (0 : BitVec 64) + sign_extend (0 : BitVec 12) = 0 := by decide
    rw [this]
  have e2 : astep code ⟨pcOf (pos + 1), gset A.regs 12 0, A.mem, A.out⟩ =
      some (.run ⟨pcOf (pos + 2), gset (gset A.regs 12 0) 13 0, A.mem, A.out⟩) := by
    rw [step_addi hfit hseg.tail.head rfl (by decide) (Has.zero _) (rd := 13) (imm := 0)]
    have : (0 : BitVec 64) + sign_extend (0 : BitVec 12) = 0 := by decide
    rw [this]
  have htgt := pcOf_lib (pos + 2) tgt (by unfold PosOK at *; omega) ht
    ((tgt : Int) - (codeBase + 4 * (pos + 2))) (by push_cast; omega)
  have htn : (BitVec.ofNat 64 tgt).toNat = tgt := by
    rw [BitVec.toNat_ofNat]; omega
  have e3 := step_lib hfit hseg.tail.tail.head
    (A := ⟨pcOf (pos + 1 + 1), gset (gset A.regs 12 0) 13 0, A.mem, A.out⟩) rfl
    (by rw [show pos + 1 + 1 = pos + 2 by omega, htgt, htn]; omega)
    (by rw [show pos + 1 + 1 = pos + 2 by omega, htgt, htn]; exact ht)
  rw [show pos + 1 + 1 = pos + 2 by omega, htgt, htn] at e3
  have l10 : lookupG 10 (gset (gset A.regs 12 0) 13 0) = some x := by
    obtain ⟨-, (⟨h, -⟩ | ⟨-, h⟩)⟩ := hx
    · cases h
    · simp [lookupG_set, h]
  have l11 : lookupG 11 (gset (gset A.regs 12 0) 13 0) = some y := by
    obtain ⟨-, (⟨h, -⟩ | ⟨-, h⟩)⟩ := hy
    · cases h
    · simp [lookupG_set, h]
  have k12 : 12 ∈ keysG (gset (gset A.regs 12 0) 13 0) :=
    mem_keysG_of_lookup (v := 0) (by simp [lookupG_set])
  have k13 : 13 ∈ keysG (gset (gset A.regs 12 0) 13 0) :=
    mem_keysG_of_lookup (v := 0) (by simp [lookupG_set])
  rw [libCall_eq tgt _ l10 l11 k12 k13 hr] at e3
  refine Star.step e1 (Star.step e2 (Star.single ?_))
  rw [e3]
  simp only [pcOf_succ]

theorem tohostW_toNat : tohostW.toNat = tohostAddr := by decide

theorem run_putcW (hfit : Fits code) {pos : Nat} {A : AM} {c : BitVec 8}
    (hseg : Seg code pos (li s3 (putcWord c) ++ li s2 tohostW ++ [.sd s3 s2]))
    (hA : A.pc = pcOf pos) :
    Star code A ⟨pcOf (pos + (li s3 (putcWord c)).length + (li s2 tohostW).length + 1),
      gset (gset A.regs s3 (putcWord c)) s2 tohostW, A.mem,
      A.out.push (toString (Char.ofNat c.toNat))⟩ := by
  obtain ⟨h12, h3⟩ := hseg.append
  obtain ⟨h1, h2⟩ := h12.append
  have r1 := run_li hfit h1 hA (by decide : 1 ≤ s3 ∧ s3 ≤ 31)
  have r2 := run_li hfit h2 (A := ⟨pcOf (pos + (li s3 (putcWord c)).length),
    gset A.regs s3 (putcWord c), A.mem, A.out⟩) rfl (by decide : 1 ≤ s2 ∧ s2 ≤ 31)
  refine r1.trans (r2.trans (Star.single ?_))
  rw [step_htif hfit h3.head (by simp [Nat.add_assoc]) (Has.set_self _ _ (by decide) (by decide))
    ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)) tohostW_toNat,
    htifOut_putc, pcOf_succ]

theorem run_putc (hfit : Fits code) {pos : Nat} {A : AM} {ch : Char} (hch : ch.toNat < 256)
    (hseg : Seg code pos (putc ch)) (hA : A.pc = pcOf pos) :
    ∃ L, Star code A ⟨pcOf (pos + (putc ch).length), L, A.mem, A.out.push (toString ch)⟩ := by
  have := run_putcW hfit (c := BitVec.ofNat 8 ch.toNat) hseg hA
  have hc : Char.ofNat (BitVec.ofNat 8 ch.toNat).toNat = ch := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hch, Char.ofNat_toNat]
  rw [hc] at this
  exact ⟨_, by simpa [putc, Nat.add_assoc] using this⟩

theorem run_exit (hfit : Fits code) {pos : Nat} {A : AM} {e : Nat} (he : e = 0 ∨ e = 70)
    (hseg : Seg code pos (exitCode e)) (hA : A.pc = pcOf pos) :
    ∃ B, Star code A B ∧ B.mem = A.mem ∧ B.out = A.out ∧ astep code B = some (.halt e) := by
  unfold exitCode at hseg
  obtain ⟨h12, h3⟩ := hseg.append
  obtain ⟨h1, h2⟩ := h12.append
  have r1 := run_li hfit h1 hA (by decide : 1 ≤ s3 ∧ s3 ≤ 31)
  have r2 := run_li hfit h2 (A := ⟨pcOf (pos + (li s3 (exitWord (BitVec.ofNat 64 e))).length),
    gset A.regs s3 (exitWord (BitVec.ofNat 64 e)), A.mem, A.out⟩) rfl (by decide : 1 ≤ s2 ∧ s2 ≤ 31)
  refine ⟨_, r1.trans r2, rfl, rfl, ?_⟩
  rw [step_htif hfit h3.head (by simp [Nat.add_assoc]) (Has.set_self _ _ (by decide) (by decide))
    ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)) tohostW_toNat,
    htifOut_exit e he]

end Vsa.Compiler

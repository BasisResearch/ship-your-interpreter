import Vsa.CT.AMTrace

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim

section
variable {code : List Ins} {pos : Nat} {A : AM}

theorem run_stageT (hfit : Fits code) {rd : Nat} {c : BitVec 12} {x : BitVec 64}
    (hseg : Seg code pos [.slli rd rd 11#6, .ori rd rd c]) (hA : A.pc = pcOf pos)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hx : Has A.regs rd x) :
    StarT code (lin pos 2) A ⟨pcOf (pos + 2), gset A.regs rd ((x <<< 11) ||| (sign_extend c : BitVec 64)),
      A.mem, A.out⟩ := by
  refine stepP hfit hseg.head trivial hA (step_slli hfit hseg.head hA hrd hx) ?_
  have e := step_ori hfit hseg.tail.head (A := ⟨pcOf (pos + 1), gset A.regs rd (x <<< 11), A.mem, A.out⟩)
    rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
  rw [gset_gset] at e
  exact singleP hfit hseg.tail.head trivial rfl e

theorem run_liT (hfit : Fits code) {rd : Nat} {n : BitVec 64} (hseg : Seg code pos (li rd n))
    (hA : A.pc = pcOf pos) (hrd : 1 ≤ rd ∧ rd ≤ 31) :
    StarT code (lin pos (li rd n).length) A
      ⟨pcOf (pos + (li rd n).length), gset A.regs rd n, A.mem, A.out⟩ := by
  by_cases hs : n.toInt < 2048 ∧ -2048 ≤ n.toInt
  · have hl : li rd n = [.addi rd 0 (BitVec.ofInt 12 n.toInt)] := by simp [li, hs]
    rw [hl] at hseg ⊢
    have e := step_addi hfit hseg.head hA hrd (Has.zero _)
    rw [sext12_ofInt _ hs.2 hs.1, BitVec.ofInt_toInt,
      show (0 : BitVec 64) + n = n by simp] at e
    exact singleP hfit hseg.head trivial hA e
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
    have t1 := run_stageT hfit (A := ⟨pcOf (pos + 1), gset A.regs rd x0, A.mem, A.out⟩)
      (by simpa using hseg.sub 1 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hy1] at t1
    have t2 := run_stageT hfit (A := ⟨pcOf (pos + 1 + 2), gset A.regs rd x1, A.mem, A.out⟩)
      (by simpa using hseg.sub 3 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hy2] at t2
    have t3 := run_stageT hfit (A := ⟨pcOf (pos + 1 + 2 + 2), gset A.regs rd x2, A.mem, A.out⟩)
      (by simpa using hseg.sub 5 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hy3] at t3
    have t4 := run_stageT hfit (A := ⟨pcOf (pos + 1 + 2 + 2 + 2), gset A.regs rd x3, A.mem, A.out⟩)
      (by simpa using hseg.sub 7 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hy4] at t4
    have t5 := run_stageT hfit (A := ⟨pcOf (pos + 1 + 2 + 2 + 2 + 2), gset A.regs rd x4, A.mem, A.out⟩)
      (by simpa using hseg.sub 9 2) rfl hrd (Has.set_self _ _ hrd.1 hrd.2)
    rw [gset_gset, hx5] at t5
    have := stepP hfit hseg.head trivial hA e0 ((((t1.trans t2).trans t3).trans t4).trans t5)
    have hlen : lin pos 11 = pobs pos :: (lin (pos + 1) 2 ++ lin (pos + 1 + 2) 2 ++
        lin (pos + 1 + 2 + 2) 2 ++ lin (pos + 1 + 2 + 2 + 2) 2 ++ lin (pos + 1 + 2 + 2 + 2 + 2) 2) := by
      simp [lin, Nat.add_assoc]
    simpa [hlen] using this

def ldTr (p a : Nat) : List Obs := lin p (liN s2 a).length ++ [mobs (p + (liN s2 a).length) a]

theorem run_ldAT (hfit : Fits code) {a rd : Nat}
    (hseg : Seg code pos (liN s2 a ++ [.ld rd s2])) (hA : A.pc = pcOf pos)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (ha : LdOK a) :
    StarT code (ldTr pos a) A ⟨pcOf (pos + (liN s2 a).length + 1),
      gset (gset A.regs s2 (BitVec.ofNat 64 a)) rd (rdW A.mem a), A.mem, A.out⟩ := by
  obtain ⟨h1, h2⟩ := hseg.append
  have hat : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; unfold LdOK at ha; omega
  refine (run_liT hfit h1 hA (by decide)).trans ?_
  have hs := Has.set_self (rd := s2) A.regs (BitVec.ofNat 64 a) (by decide) (by decide)
  have e := step_ld hfit h2.head rfl hrd hs (by rw [hat]; exact ha)
    (A := ⟨pcOf (pos + (liN s2 a).length), gset A.regs s2 (BitVec.ofNat 64 a), A.mem, A.out⟩)
  rw [hat] at e
  have := stepM hfit h2.head rfl e (.refl _)
  simp only [insObs, hs.src.2, hat] at this
  exact this

def stTr (p a : Nat) : List Obs := lin p (liN s2 a).length ++ [mobs (p + (liN s2 a).length) a]

theorem run_stAT (hfit : Fits code) {a rs : Nat} {w : BitVec 64}
    (hseg : Seg code pos (liN s2 a ++ [.sd rs s2])) (hA : A.pc = pcOf pos)
    (hw : Has A.regs rs w) (hrs : rs ≠ s2) (ha : StOK a) :
    StarT code (stTr pos a) A ⟨pcOf (pos + (liN s2 a).length + 1),
      gset A.regs s2 (BitVec.ofNat 64 a), applyW A.mem (a, 8, w), A.out⟩ := by
  obtain ⟨h1, h2⟩ := hseg.append
  have hat : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; unfold StOK at ha; omega
  refine (run_liT hfit h1 hA (by decide)).trans ?_
  have hs := Has.set_self (rd := s2) A.regs (BitVec.ofNat 64 a) (by decide) (by decide)
  have e := step_sd hfit h2.head rfl hs (hw.set_other hrs) (by rw [hat]; exact ha)
    (A := ⟨pcOf (pos + (liN s2 a).length), gset A.regs s2 (BitVec.ofNat 64 a), A.mem, A.out⟩)
  rw [hat] at e
  have := stepM hfit h2.head rfl e (.refl _)
  simp only [insObs, hs.src.2, hat] at this
  exact this

def libcTr (p t : Nat) (x y : BitVec 64) : List Obs := [pobs p, pobs (p + 1), lobs (p + 2) t x y]

theorem run_libcT (hfit : Fits code) {tgt : Nat} {x y r : BitVec 64}
    (hseg : Seg code pos (libc pos tgt)) (hA : A.pc = pcOf pos) (hp : PosOK (pos + 3))
    (ht : tgt = mulPC ∨ tgt = divPC ∨ tgt = modPC)
    (hx : Has A.regs 10 x) (hy : Has A.regs 11 y) (hr : libRes tgt x y = some r) :
    StarT code (libcTr pos tgt x y) A ⟨pcOf (pos + 3), (10, r) :: eraseAll clobbered
      (gset (gset A.regs 12 0) 13 0), A.mem, A.out⟩ := by
  have hb : codeBase = 0x80004800 := rfl
  have htt : tohostAddr = 0x8001ad00 := rfl
  have hm : mulPC = 0x80004640 := rfl
  have hd : divPC = 0x800046a4 := rfl
  have hmo : modPC = 0x80004728 := rfl
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
  have hk3 : code[pos + 2]? = some (Ins.jal ra (BitVec.ofInt 21 ((tgt : Int) -
      (codeBase + 4 * (pos + 2))))) := by
    simpa using hseg.tail.tail.head
  have e3 := step_lib hfit hk3 (A := ⟨pcOf (pos + 2), gset (gset A.regs 12 0) 13 0, A.mem, A.out⟩) rfl
    (by rw [htgt, htn]; omega) (by rw [htgt, htn]; exact ht)
  rw [htgt, htn] at e3
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
  simp only [pcOf_succ] at e3
  have s3 := stepM hfit hk3 rfl e3 (.refl _)
  have hx' : srcVal 10 (gset (gset A.regs 12 0) 13 0) = x :=
    (show Has _ 10 x from ⟨by decide, .inr ⟨by decide, l10⟩⟩).src.2
  have hy' : srcVal 11 (gset (gset A.regs 12 0) 13 0) = y :=
    (show Has _ 11 y from ⟨by decide, .inr ⟨by decide, l11⟩⟩).src.2
  have hlib : isLibT (pcOf (pos + 2) + (sign_extend (evenJ (BitVec.ofInt 21 ((tgt : Int) -
      (codeBase + 4 * (pos + 2))))) : BitVec 64)).toNat := by
    rw [htgt, htn]; exact ht
  have hlib' : isLibT tgt := ht
  simp only [insObs, ra, hx', hy', htgt, htn, true_and, hlib', if_true] at s3
  exact stepP hfit hseg.head trivial hA e1 (stepP hfit hseg.tail.head trivial rfl e2 s3)

def putcTr (p : Nat) (c : BitVec 8) : List Obs :=
  lin p (li s3 (putcWord c)).length ++ lin (p + (li s3 (putcWord c)).length) (li s2 tohostW).length ++
    [mobs (p + (li s3 (putcWord c)).length + (li s2 tohostW).length) tohostAddr]

theorem run_putcWT (hfit : Fits code) {c : BitVec 8}
    (hseg : Seg code pos (li s3 (putcWord c) ++ li s2 tohostW ++ [.sd s3 s2]))
    (hA : A.pc = pcOf pos) :
    StarT code (putcTr pos c) A ⟨pcOf (pos + (li s3 (putcWord c)).length + (li s2 tohostW).length + 1),
      gset (gset A.regs s3 (putcWord c)) s2 tohostW, A.mem,
      A.out.push (toString (Char.ofNat c.toNat))⟩ := by
  obtain ⟨h12, h3⟩ := hseg.append
  obtain ⟨h1, h2⟩ := h12.append
  have r1 := run_liT hfit h1 hA (by decide : 1 ≤ s3 ∧ s3 ≤ 31)
  have r2 := run_liT hfit h2 (A := ⟨pcOf (pos + (li s3 (putcWord c)).length),
    gset A.regs s3 (putcWord c), A.mem, A.out⟩) rfl (by decide : 1 ≤ s2 ∧ s2 ≤ 31)
  have hs2 := Has.set_self (rd := s2) (gset A.regs s3 (putcWord c)) tohostW (by decide) (by decide)
  have e := step_htif hfit h3.head (by simp [Nat.add_assoc]) hs2
    ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)) tohostW_toNat
    (A := ⟨pcOf (pos + (li s3 (putcWord c)).length + (li s2 tohostW).length),
      gset (gset A.regs s3 (putcWord c)) s2 tohostW, A.mem, A.out⟩)
  rw [htifOut_putc, pcOf_succ] at e
  have s3' := stepM hfit h3.head (by simp [Nat.add_assoc]) e (.refl _)
  simp only [insObs, hs2.src.2, tohostW_toNat] at s3'
  have := r1.trans (r2.trans s3')
  simpa [putcTr, List.append_assoc, mobs] using this

theorem run_putcT (hfit : Fits code) {ch : Char} (hch : ch.toNat < 256)
    (hseg : Seg code pos (putc ch)) (hA : A.pc = pcOf pos) :
    ∃ L, StarT code (putcTr pos (BitVec.ofNat 8 ch.toNat)) A
      ⟨pcOf (pos + (putc ch).length), L, A.mem, A.out.push (toString ch)⟩ := by
  have := run_putcWT hfit (c := BitVec.ofNat 8 ch.toNat) hseg hA
  have hc : Char.ofNat (BitVec.ofNat 8 ch.toNat).toNat = ch := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hch, Char.ofNat_toNat]
  rw [hc] at this
  exact ⟨_, by simpa [putc, Nat.add_assoc] using this⟩

def exitTr (p e : Nat) : List Obs :=
  lin p (li s3 (exitWord (BitVec.ofNat 64 e))).length ++
    lin (p + (li s3 (exitWord (BitVec.ofNat 64 e))).length) (li s2 tohostW).length

theorem run_exitT (hfit : Fits code) {e : Nat} (he : e = 0 ∨ e = 70)
    (hseg : Seg code pos (exitCode e)) (hA : A.pc = pcOf pos) :
    ∃ B, StarT code (exitTr pos e) A B ∧ B.mem = A.mem ∧ B.out = A.out ∧
      astep code B = some (.halt e) := by
  unfold exitCode at hseg
  obtain ⟨h12, h3⟩ := hseg.append
  obtain ⟨h1, h2⟩ := h12.append
  have r1 := run_liT hfit h1 hA (by decide : 1 ≤ s3 ∧ s3 ≤ 31)
  have r2 := run_liT hfit h2 (A := ⟨pcOf (pos + (li s3 (exitWord (BitVec.ofNat 64 e))).length),
    gset A.regs s3 (exitWord (BitVec.ofNat 64 e)), A.mem, A.out⟩) rfl (by decide : 1 ≤ s2 ∧ s2 ≤ 31)
  refine ⟨_, r1.trans r2, rfl, rfl, ?_⟩
  rw [step_htif hfit h3.head (by simp [Nat.add_assoc]) (Has.set_self _ _ (by decide) (by decide))
    ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)) tohostW_toNat,
    htifOut_exit e he]

theorem jumpT (hfit : Fits code) {p q : Nat}
    (hk : code[p]? = some (.jal 0 (jOff p q))) (hA : A.pc = pcOf p) (hp : PosOK p) (hq : PosOK q) :
    StarT code [pobs p] A ⟨pcOf q, A.regs, A.mem, A.out⟩ := by
  have := stepM hfit hk hA (step_jump hfit hk hA hp hq) (.refl _)
  simpa [insObs, hA, pobs] using this

def condTr (q : Nat) (b : Bool) : List Obs := if b then [pobs q] else [pobs q, pobs (q + 1)]

theorem run_condT (hfit : Fits code) {q L : Nat} {w : BitVec 64}
    (hseg : Seg code q [.br .ne a0 0 (bSkip 1), .jal 0 (jOff (q + 1) L)])
    (hA : A.pc = pcOf q) (hq : PosOK (q + 2)) (hL : PosOK L) (h0 : Has A.regs a0 w) :
    StarT code (condTr q (!(w == 0))) A ⟨pcOf (if w = 0 then L else q + 2), A.regs, A.mem, A.out⟩ := by
  have hb : codeBase = 0x80004800 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hs := pcOf_skip q 1 (by unfold PosOK at *; omega) (by decide)
  have e1 := step_br hfit hseg.head hA h0 (Has.zero _)
    (by rw [hs, pcOf_toNat (by unfold PosOK at *; omega)]; omega)
  rw [hs] at e1
  by_cases hw : w = 0
  · subst hw
    have hg : guardB BrOp.ne.bop (0 : BitVec 64) 0 = false := by decide
    rw [hg] at e1
    simp only [Bool.false_eq_true, if_false] at e1
    rw [if_pos rfl]
    have := stepP hfit hseg.head trivial hA e1
      (jumpT hfit hseg.tail.head rfl (by unfold PosOK at *; omega) hL)
    simpa [condTr] using this
  · have hg : guardB BrOp.ne.bop w 0 = true := by simp only [BrOp.bop, guardB]; simpa using hw
    rw [hg, if_pos rfl] at e1
    rw [if_neg hw]
    have := singleP hfit hseg.head trivial hA e1
    rw [show q + 1 + 1 = q + 2 by omega] at this
    have hw' : (w == 0) = false := by simpa using hw
    simp only [condTr, hw', Bool.not_false, ite_true]
    exact this

end

end Vsa.Compiler

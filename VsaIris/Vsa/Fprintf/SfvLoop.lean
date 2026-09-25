import VsaIris.Vsa.Fprintf.Sfv

/-!
# `__sfvwrite_r`'s loop on `__sbprintf`'s stack `FILE` (lane N5)

The loop over the `uio`'s pieces, by induction on the bytes and pieces left
(`sfv_loop`). The state at the head is the current piece `(src, bs)`, the
pieces after it (`rest`, an `iov` array at `nxt`), the buffered bytes `pend`
(`SbFile`) and the bytes already printed `done`, with

    pend0 ++ ALL = done ++ pend ++ bs ++ (rest's bytes),

the memory changed from the loop's base `Mb` only inside `LoopReg` (the
pass region `SfvReg` and the `uio`'s residual). Each pass is a fetch
(`sfv_fetch`), a copy (`sfv_copyA` → `memmove_run` → `sfv_copyB`) or a
direct write (`sfv_direct`), then the tail (`sfv_tail`) back to the head or
out (`sfv_exit`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- The bytes the loop changes: a pass's (`SfvReg`) and the residual. -/
def LoopReg (f fp U : Nat) (a : Nat) : Prop := SfvReg f fp a ∨ (U + 16 ≤ a ∧ a < U + 24)

/-- The loop's placement: `__sfvwrite_r`'s frame at `fp` in the call's stack
window, the `FILE` (with its buffer) and the `uio` above it. -/
structure SfvGeom (s fp f U : BitVec 64) (need : Nat) : Prop where
  hs1 : s.toNat - need + 256 ≤ fp.toNat
  hs2 : fp.toNat + 96 ≤ s.toNat
  hs3 : s.toNat ≤ 0x88000000
  hs4 : 0x80100000 ≤ s.toNat - need
  hfpa : fp.toNat % 16 = 0
  hf1 : fp.toNat + 96 ≤ f.toNat
  hf2 : f.toNat + 1208 ≤ s.toNat
  hfa : f.toNat % 8 = 0
  hU1 : fp.toNat + 96 ≤ U.toNat
  hU2 : U.toNat + 24 ≤ s.toNat
  hUa : U.toNat % 8 = 0
  hfU : U.toNat + 24 ≤ f.toNat ∨ f.toNat + 1208 ≤ U.toNat

/-- A piece's source: RAM, off the HTIF words, outside what the loop changes. -/
structure SrcOK (f fp U : Nat) (src len : Nat) : Prop where
  lo : 0x80000000 ≤ src
  hi : src + len ≤ 0x100000000
  htif : src + len ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ src
  out : ∀ i, i < len → ¬ LoopReg f fp U (src + i)

/-- The `iov` entries of the pieces `rest` from `nxt`. -/
def IovAt (M : Mem) (nxt : Nat) (rest : List (Nat × List (BitVec 8))) : Prop :=
  ∀ j (h : j < rest.length), ldv .ld M (BitVec.ofNat 64 (nxt + 16 * j)).toNat = BitVec.ofNat 64 rest[j].1 ∧
    ldv .ld M (BitVec.ofNat 64 (nxt + 16 * j + 8)).toNat = BitVec.ofNat 64 rest[j].2.length

/-- The bytes of a list of pieces. -/
def piecesBytes (rest : List (Nat × List (BitVec 8))) : List (BitVec 8) := (rest.map Prod.snd).flatten

/-- The byte count of a list of pieces. -/
def piecesLen (rest : List (Nat × List (BitVec 8))) : Nat := (rest.map fun p => p.2.length).sum

theorem piecesLen_eq (rest : List (Nat × List (BitVec 8))) : piecesLen rest = (piecesBytes rest).length := by
  induction rest with
  | nil => rfl
  | cons p rest ih => simp [piecesLen, piecesBytes] at *; omega

/-- The stack `FILE` survives a change off its bytes, `stdout`'s flags and
descriptor and `_impure_data.__cleanup`. -/
theorem SbFile.frame_out {M M' : Mem} {f : BitVec 64} {pend : List (BitVec 8)} {Reg : Nat → Prop}
    (hF : SbFile M f pend) (hFr : Frame M' M Reg) (hf : f.toNat + 1208 < 2 ^ 64)
    (hR : ∀ b, Reg b → (b < f.toNat ∨ f.toNat + 1208 ≤ b) ∧ (b < 0x8001bb30 ∨ 0x8001bb34 ≤ b) ∧
      (b < 0x8001b580 ∨ 0x8001b588 ≤ b)) : SbFile M' f pend := by
  have hlt := hF.len
  have e : ∀ n, n < 1208 → (f + BitVec.ofNat 64 n).toNat = f.toNat + n := fun n hn => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show f.toNat + n < 2 ^ 64 by omega)]
  have out : ∀ (k : MKind) (n : Nat), n + 8 ≤ 1208 → ldv k M' (f + BitVec.ofNat 64 n).toNat =
      ldv k M (f + BitVec.ofNat 64 n).toNat := fun k n hn => by
    have hw : widthOfM k ≤ 8 := by cases k <;> simp [widthOfM]
    refine hFr.ldv k fun j hj hr => ?_
    have := hR _ hr; rw [e n (by omega)] at this; omega
  have outA : ∀ (k : MKind) (a : Nat), (0x8001bb30 ≤ a ∧ a + widthOfM k ≤ 0x8001bb34) ∨
      (0x8001b580 ≤ a ∧ a + widthOfM k ≤ 0x8001b588) → ldv k M' a = ldv k M a := fun k a ha => by
    refine hFr.ldv k fun j hj hr => ?_
    have := hR _ hr; omega
  have out0 : ldv .ld M' f.toNat = ldv .ld M f.toNat := by
    have := out .ld 0 (by omega); simpa using this
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hF.len, ?_, ?_, fun i h => ?_⟩
  · rw [out .lh 16 (by omega)]; exact hF.flags
  · rw [out .lhu 16 (by omega)]; exact hF.flagsU
  · rw [out .ld 24 (by omega)]; exact hF.base
  · rw [out .lw 32 (by omega)]; exact hF.size
  · rw [out .ld 48 (by omega)]; exact hF.cookie
  · rw [out .ld 64 (by omega)]; exact hF.writer
  · rw [out .lw 176 (by omega)]; exact hF.flags2
  · rw [outA .lh _ (.inl ⟨Nat.le_refl _, by simp [widthOfM]⟩)]; exact hF.sfl
  · rw [outA .lh _ (.inl ⟨by omega, by simp [widthOfM]⟩)]; exact hF.sfd
  · rw [outA .ld _ (.inr ⟨Nat.le_refl _, by simp [widthOfM]⟩)]; exact hF.sinit
  · rw [out0]; exact hF.p
  · rw [out .lw 12 (by omega)]; exact hF.w
  · rw [hFr _ (fun hr => by have := hR _ hr; rw [e 184 (by omega)] at this; omega)]; exact hF.buf i h

/-- The spills survive a change off `[fp, fp + 96)`. -/
theorem SfvSpills.frame_out {M M' : Mem} {fp : BitVec 64} {R0 : Nat → BitVec 64} {Reg : Nat → Prop}
    (h : SfvSpills M fp R0) (hFr : Frame M' M Reg) (hfp : fp.toNat + 96 < 2 ^ 64)
    (hR : ∀ b, Reg b → b < fp.toNat ∨ fp.toNat + 96 ≤ b) : SfvSpills M' fp R0 := by
  have out : ∀ n, n + 8 ≤ 96 → ldv .ld M' (fp + BitVec.ofNat 64 n).toNat = ldv .ld M (fp + BitVec.ofNat 64 n).toNat :=
    fun n hn => by
      have e : (fp + BitVec.ofNat 64 n).toNat = fp.toNat + n := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show fp.toNat + n < 2 ^ 64 by omega)]
      refine hFr.ldv .ld fun j hj hr => ?_
      have := hR _ hr; simp only [widthOfM] at hj; rw [e] at this; omega
  exact ⟨by rw [out 88 (by omega)]; exact h.ra, by rw [out 80 (by omega)]; exact h.s0,
    by rw [out 72 (by omega)]; exact h.s1, by rw [out 64 (by omega)]; exact h.s2,
    by rw [out 56 (by omega)]; exact h.s3, by rw [out 48 (by omega)]; exact h.s4,
    by rw [out 40 (by omega)]; exact h.s5, by rw [out 32 (by omega)]; exact h.s6,
    by rw [out 24 (by omega)]; exact h.s7, by rw [out 16 (by omega)]; exact h.s8,
    by rw [out 8 (by omega)]; exact h.s9⟩

theorem add_ofNat_eq {f : BitVec 64} {n : Nat} : f + BitVec.ofNat 64 n = BitVec.ofNat 64 (f.toNat + n) := by
  rw [← ofNat_add_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **`__sfvwrite_r`'s loop** from its head, by induction on the pieces and
bytes left. On the way out (`__sfvwrite_r` returns 0 to the entry's `ra`)
the continuation `hk` gets the printed bytes `out` and the buffered `pend'`
with `pend0 ++ ALL = out ++ pend'`. -/
theorem sfv_loop (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA)
    {s fp f U : BitVec 64} {need : Nat} {Rh R0 : Nat → BitVec 64} {Mb : Mem}
    (G : SfvGeom s fp f U need) (hRh : SfvRef Rh f U fp) (hsp : SfvSpills Mb fp R0)
    (h0 : R0 2 = fp + 96#64) (hra : (R0 1).toNat % 4 = 0) (h26 : Rh 26 = R0 26) (h27 : Rh 27 = R0 27)
    (pend0 ALL : List (BitVec 8)) (t0 : String)
    (hk : ∀ R' M' out pend', pend0 ++ ALL = out ++ pend' → RetOK R0 R' 0#64 → SbFile M' f pend' →
      Frame M' Mb (LoopReg f.toNat fp.toNat U.toNat) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t0 ++ putcs out) (R0 1) R' M') :
    ∀ n (done pend bs : List (BitVec 8)) (src nxt : Nat) (rest : List (Nat × List (BitVec 8)))
      (R : Nat → BitVec 64) (M : Mem), bs.length + piecesLen rest + rest.length < n →
      pend0 ++ ALL = done ++ (pend ++ bs ++ piecesBytes rest) → 0 < bs.length + piecesLen rest →
      bs.length + piecesLen rest < 2 ^ 31 →
      SfvRegs R Rh nxt bs.length src (f + BitVec.ofNat 64 (184 + pend.length)) → SbFile M f pend →
      Frame M Mb (LoopReg f.toNat fp.toNat U.toNat) →
      ldv .ld M (U + 16#64).toNat = BitVec.ofNat 64 (bs.length + piecesLen rest) →
      IovAt Mb nxt rest → (s.toNat - need ≤ nxt ∧ nxt + 16 * rest.length ≤ s.toNat ∧ nxt % 8 = 0 ∧
        ∀ a, nxt ≤ a → a < nxt + 16 * rest.length → ¬ LoopReg f.toNat fp.toNat U.toNat a) →
      PieceReads Dt DA (outS s need) Mb src bs → SrcOK f.toNat fp.toNat U.toNat src bs.length →
      (∀ p ∈ rest, PieceReads Dt DA (outS s need) Mb p.1 p.2 ∧ SrcOK f.toNat fp.toNat U.toNat p.1 p.2.length) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t0 ++ putcs done) 0x8000dfc0#64 R M := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; omega
  | succ n ih =>
    intro done pend bs src nxt rest R M hμ hrel hpos hsmall hR hF hFr hres hiov hnxt hsrc hsok hrest
    have hfsz : f.toNat + 1208 < 2 ^ 32 := by have := G.hf2; have := G.hs3; omega
    -- a pass of `c` bytes ends at the tail: back to the head, or out
    have tailK : ∀ (c : Nat) (R3 : Nat → BitVec 64) (M3 : Mem) (pend' out : List (BitVec 8)),
        0 < c → c ≤ bs.length → pend ++ bs.take c = out ++ pend' →
        R3 18 = BitVec.ofNat 64 c → R3 9 = BitVec.ofNat 64 nxt → R3 19 = BitVec.ofNat 64 bs.length →
        R3 22 = BitVec.ofNat 64 src → (∀ x ∈ sfvKeep, R3 x = Rh x) → SbFile M3 f pend' →
        Frame M3 M (SfvReg f.toNat fp.toNat) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t0 ++ putcs done ++ putcs out)
          0x8000e258#64 R3 M3 := by
      intro c R3 M3 pend' out hc0 hcL hsplit h18 h9 h19 h22 hkeep hF3 hFr3
      have hres3 : ldv .ld M3 (U + 16#64).toNat = BitVec.ofNat 64 (bs.length + piecesLen rest) := by
        rw [hFr3.ldv .ld (fun j hj hr => by
          simp only [widthOfM] at hj
          have e : (U + 16#64).toNat = U.toNat + 16 := by
            rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := G.hU2; have := G.hs3; omega
          rw [e] at hr; unfold SfvReg at hr; have := G.hfU; have := G.hU1; have := G.hf1; have := G.hs1
          have := G.hs4; omega)]
        exact hres
      have hU16 : (U + 16#64).toNat = U.toNat + 16 := by
        rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := G.hU2; have := G.hs3; omega
      -- the memory after the residual store, from the base
      have hFr4 : Frame (writeLog M3 [((U + 16#64).toNat, 8, BitVec.ofNat 64 (bs.length + piecesLen rest - c))])
          Mb (LoopReg f.toNat fp.toNat U.toNat) :=
        (hFr.trans (hFr3.mono fun a h => .inl h)).snoc fun b h1 h2 => .inr (by omega)
      have hF4 : SbFile (writeLog M3 [((U + 16#64).toNat, 8, BitVec.ofNat 64 (bs.length + piecesLen rest - c))])
          f pend' :=
        hF3.frame_out (Frame.store M3 _ (Reg := fun b => U.toNat + 16 ≤ b ∧ b < U.toNat + 24)
          fun b h1 h2 => by omega) (by omega) fun b hb => by
            have := G.hfU; have := G.hU1; have := G.hs1; have := G.hs4; omega
      rw [String.append_assoc, ← putcs_append]
      refine sfv_tail (P := ldv .ld M3 f.toNat) (resid := bs.length + piecesLen rest) hlive G.hs3 G.hs4
        (by have := G.hU1; have := G.hs1; omega) G.hU2 G.hUa (by have := G.hf1; have := G.hs1; omega) G.hf2
        G.hfU (by omega) (by omega) hcL (by omega) (by have := hsok.hi; omega) hRh h9 h19 h22 hkeep h18 hres3
        hF3.flags rfl (fun hne R' hR' => ?_) (fun heq R' hkeep' => ?_)
      · -- back to the head
        rw [hF3.p] at hR'
        refine ih (done ++ out) pend' (bs.drop c) (src + c) nxt rest R' _ ?_ ?_ ?_ ?_ (by simpa using hR')
          hF4 hFr4 ?_ hiov hnxt (hsrc.drop c) ⟨by have := hsok.lo; omega, by have := hsok.hi; simp; omega,
            by have := hsok.htif; simp; omega, fun i hi => by
              simp at hi; rw [Nat.add_assoc]; exact hsok.out (c + i) (by omega)⟩ hrest
        · simp; omega
        · rw [hrel, List.append_assoc, ← List.take_append_drop c bs, List.append_assoc, ← List.append_assoc pend,
            hsplit]; simp [List.append_assoc]
        · simp; omega
        · simp; omega
        · rw [ldv_store_hit]; congr 1; simp; omega
      · -- the residual is zero: out
        refine sfv_exit hlive G.hs3 G.hs4 (by have := G.hs1; omega) G.hs2 G.hfpa
          ((hkeep' 2 (by decide)).trans hRh.sp) h0 hra ((hkeep' 26 (by decide)).trans h26)
          ((hkeep' 27 (by decide)).trans h27) (hsp.frame_out hFr4 (by have := G.hs2; have := G.hs3; omega)
            fun b hb => by
              unfold LoopReg SfvReg at hb; have := G.hf1; have := G.hU1; have := G.hs1; have := G.hs4; omega)
          (fun R'' hret => hk R'' _ (done ++ out) pend' ?_ hret hF4 hFr4)
        have hbc : bs.length = c := by have := hcL; have := piecesLen_eq rest; omega
        have hpr : piecesBytes rest = [] := by
          apply List.eq_nil_of_length_eq_zero; rw [← piecesLen_eq]; omega
        rw [hrel, hpr, List.append_nil, List.append_assoc, ← hsplit, ← hbc, List.take_length]
    rcases Nat.eq_zero_or_pos bs.length with hL0 | hL0
    · -- the current piece is used up: fetch the next
      obtain ⟨hn1, hn2, hna, hnreg⟩ := hnxt
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero hL0
      subst hbs
      match rest, hrest, hiov, hn2, hnreg, hpos, hμ, hrel, hres with
      | [], _, _, _, _, hpos, _, _, _ => simp [piecesLen] at hpos
      | p :: rest', hrest, hiov, hn2, hnreg, hpos, hμ, hrel, hres =>
        have hp := hrest p (List.mem_cons_self)
        obtain ⟨hs0, hl0⟩ := hiov 0 (by simp)
        simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at hs0 hl0
        have hnr : ∀ k, k < 16 → ¬ LoopReg f.toNat fp.toNat U.toNat (nxt + k) := fun k hk =>
          hnreg _ (by omega) (by simp at hn2 ⊢; omega)
        have hnd : (BitVec.ofNat 64 nxt).toNat = nxt := by simp only [BitVec.toNat_ofNat]; omega
        have hnd8 : (BitVec.ofNat 64 (nxt + 8)).toNat = nxt + 8 := by
          simp only [BitVec.toNat_ofNat]; simp at hn2; omega
        refine sfv_fetch (src' := p.1) (L' := p.2.length) hlive G.hs3 G.hs4 hn1 (by simp at hn2; omega) hna
          hRh (by simpa using hR) ?_ ?_ (fun R' hR' => ?_)
        · rw [hFr.ldv .ld (fun j hj => by simp only [widthOfM] at hj; rw [hnd]; exact hnr j (by omega))]
          exact hs0
        · rw [hFr.ldv .ld (fun j hj => by simp only [widthOfM] at hj; rw [hnd8, Nat.add_assoc]; exact hnr (8 + j) (by omega))]
          exact hl0
        · refine ih done pend p.2 p.1 (nxt + 16) rest' R' M ?_ ?_ ?_ ?_ hR' hF hFr ?_ ?_ ?_ hp.1 hp.2 ?_
          · simp [piecesLen] at hμ ⊢; omega
          · rw [hrel]; simp [piecesBytes]
          · simpa [piecesLen] using hpos
          · simpa [piecesLen] using hsmall
          · rw [hres]; simp [piecesLen]
          · intro j hj
            have := hiov (j + 1) (by simp; omega)
            simp only [List.getElem_cons_succ] at this
            rw [show nxt + 16 + 16 * j = nxt + 16 * (j + 1) by omega]
            exact this
          · simp at hn2
            exact ⟨by omega, by omega, by omega, fun a h1 h2 => hnreg a (by omega) (by simp; omega)⟩
          · intro q hq; exact hrest q (List.mem_cons_of_mem _ hq)
    · by_cases hdir : pend.length = 0 ∧ 1024 ≤ bs.length
      · -- a direct write
        obtain ⟨hk0, hL1⟩ := hdir
        have hp0 : pend = [] := List.eq_nil_of_length_eq_zero hk0
        subst hp0
        have hsrcM : PieceReads Dt DA (outS s need) M src bs :=
          hsrc.transport fun i hi => hFr _ (hsok.out i hi)
        refine sfv_direct hlive hlive' hsub G.hs1 (by have := G.hs2; omega) G.hs3 G.hs4 G.hfpa
          (by have := G.hf1; omega) G.hf2 G.hfa hL1 (by omega) hsok.lo hsok.hi
          (by have := hsok.htif; unfold tohostAddr; omega)
          (fun i hi => by have := hsok.out i hi; unfold LoopReg SfvReg at this; omega)
          hsrcM.readWin hRh (by simpa using hR) hF (fun R' M' h18 h9 h19 h22 hkeep hF' hFr' => ?_)
        rw [copyBytes_win _ _ _ (by omega)]
        exact tailK _ R' M' [] _ (by omega) (by omega) (by simp) h18 h9 h19 h22 hkeep hF' hFr'
      · -- a copy into the buffer
        have hroom : 0 < pend.length ∨ bs.length < 1024 := by omega
        have hk1024 := hF.len
        have hB : (f + 184#64).toNat = f.toNat + 184 := by
          rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
        have hsrcM : PieceReads Dt DA (outS s need) M src bs :=
          hsrc.transport fun i hi => hFr _ (hsok.out i hi)
        have hc0 : 0 < min bs.length (1024 - pend.length) := by omega
        refine sfv_copyA hlive G.hs3 G.hs4 (by have := G.hf1; have := G.hs1; omega) G.hf2 G.hfa hF.len hL0
          (by omega) hroom hRh hR hF.w hF.base hF.size (fun R1 h10 h11 h12 h18 h1 hR1 => ?_)
        have hd : BitVec.ofNat 64 ((f + 184#64).toNat + pend.length) = f + BitVec.ofNat 64 (184 + pend.length) := by
          rw [hB, add_ofNat_eq, Nat.add_assoc]
        refine memmove_run hlive ((f + 184#64).toNat + pend.length) src (min bs.length (1024 - pend.length))
          (win bs src) R1 M ⟨?_, ?_, ?_, hsok.lo, ?_, ?_, ?_⟩ ?_ (by rw [h10, hd]) h11 h12 (by rw [h1]; decide)
          (fun R2 M2 hmm hcp => ?_)
        · rw [hB]; have := G.hf1; have := G.hs1; have := G.hs4; omega
        · rw [hB]; have := G.hs3; omega
        · intro b h1 h2; rw [hB] at h1 h2; have := G.hf2; have := G.hf1; have := G.hs1; unfold outS; omega
        · have := hsok.hi; omega
        · have := hsok.htif; omega
        · have h0 := hsok.out 0 hL0
          have hc := hsok.out (min bs.length (1024 - pend.length) - 1) (by omega)
          unfold LoopReg SfvReg at h0 hc; rw [hB]; omega
        · exact fun a h1 h2 => hsrcM.readWin a h1 (by omega)
        rw [h1]
        have hmk : ∀ z, z ≠ 11 → z ≠ 12 → z ≠ 13 → z ≠ 14 → z ≠ 15 → z ≠ 16 → z ≠ 17 → z ≠ 6 → z ≠ 28 →
            R2 z = R1 z := hmm
        refine sfv_copyB hlive G.hs1 (by have := G.hs2; omega) G.hs3 G.hs4 G.hfpa (by have := G.hf1; omega)
          G.hf2 G.hfa hc0 (by omega) hRh ?_ (by rw [hmk 9 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hR1.nxt)
          (by rw [hmk 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact hR1.len)
          (by rw [hmk 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact hR1.src)
          (by rw [hmk 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact h18) hF hcp
          (fun R3 M3 pend' out hsplit h18' h9' h19' h22' hkeep' hF3 hFr3 => ?_)
        · intro x hx
          rw [hmk x (by simp [sfvKeep] at hx; omega) (by simp [sfvKeep] at hx; omega)
            (by simp [sfvKeep] at hx; omega) (by simp [sfvKeep] at hx; omega) (by simp [sfvKeep] at hx; omega)
            (by simp [sfvKeep] at hx; omega) (by simp [sfvKeep] at hx; omega) (by simp [sfvKeep] at hx; omega)
            (by simp [sfvKeep] at hx; omega)]
          exact hR1.keep x hx
        rw [copyBytes_win _ _ _ (by omega)] at hsplit
        exact tailK _ R3 M3 pend' out hc0 (by omega) hsplit h18' h9' h19' h22' hkeep' hF3 hFr3

end VsaIris.Sym.Fp

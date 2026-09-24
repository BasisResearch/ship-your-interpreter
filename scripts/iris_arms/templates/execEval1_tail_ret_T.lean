  have hcopy := wp_execRetCopy (N := N) (L := L) (Room := Room) (inp := inp) hlive (twpW _)
    (Φ := Φ) (ρ := .counted k) (st' := st') (d := d) (sm := {SM}) (v := v) (aRet := aRet)
    (s := s) (ret := ret) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (w0 := w0) (w1 := w1)
    (w2 := w2) (R0 := R) (R := upd R1 1 (BitVec.ofNat 64 (0x{J1} + 4)))
    (Mt := slotWrite Mt1 (execSP s + 16#64).toNat w0 w1 w2) hf.stack hf.slot hf.ral
    (by subst hR0; ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hf.regs.sp)
    (by subst hR0; ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hf.regs.s2)
    hsv1 hk1
    (by rw [← g1]; ix_fwd)
    (by rw [show s.toNat - 176 + 24 = (execSP s + 16#64).toNat + 8 by omega]; ix_fwd)
    (by rw [show s.toNat - 176 + 32 = (execSP s + 16#64).toNat + 16 by omega]; ix_fwd)
  iapply hcopy
  iframe Hcode Hms Hslot Hv1 Hst Hw HK

import VsaIris.Vsa.Stdout.Swbuf

/-!
# `fputc(c, stdout)` as a symbolic run (lane N1)

From the boundary state (`ConsoleMt`): `fputc` takes the (no-op) lock,
calls `_putc_r`, which takes it again, finds `_w` exhausted and calls
`__swbuf_r` (`swbuf_run`), which prints `c`; both release and return `c`.
-/

namespace VsaIris.Sym

open scoped VsaIris.Sym.Stdout

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- The lock tests' `_flags & __SSTR` (`andi …,512`) is clear at either
orientation. -/
theorem consoleFlagsV_and512 (o : Bool) : consoleFlagsV o &&& 512#64 = 0#64 := by
  cases o <;> decide

#ix_seg fputc_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1)
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s ra : BitVec 64} {need : Nat} {c : BitVec 8}
    (hs1 : s.toNat - need + 512 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h10 : R 10 = BitVec.zeroExtend 64 c) (h11 : R 11 = 0x8001bb20#64) (h2 : R 2 = s)
    {o : Bool} (hc : ConsoleMt (consoleFlagsV o) Mt) :
    SWPO live (stdioText ++ dataOf impDt (accAddrs 0x8001b970 8)) iRegs (outS s need) Q t 0x800062e0#64 R Mt
  by nx_run hlive using [h1, h10, h11, h2, consoleFlagsV_and512, BitVec.add_assoc] at 2147542692

#ix_piece fputc_A2 from fputc_A by
  nx_run hlive using [h1, h10, h11, h2, consoleFlagsV_and512, BitVec.add_assoc] at 2147545288

#ix_piece fputc_B from fputc_A2 by
  refine swbuf_run' (sp := s + 18446744073709551536#64) (ra := 0x8000e740#64) (c := c) (o := o) hlive
    ?_ ?_ hs3 hs4 ?_ (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun R' M' hR hK hD => ?_)
  all_goals try (nx_norm; done)
  all_goals try nx_addr
  all_goals try ((try nx_norm); nx_mem; nx_console; done)

#ix_piece fputc_C from fputc_B by
  nx_ret hR
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, h1, hD.p, hD.w, hD.flagsU, hD.flagsS,
    BitVec.add_assoc]

#nx_chain fputc_chain := [fputc_A, fputc_A2, fputc_B, fputc_C]

/-- **`fputc(c, stdout)`** from the boundary state: prints `c`, returns it;
the memory keeps `outKeep s 512` and ends with `stdout` idle (`OutDone`). -/
theorem fputc_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1)
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s ra : BitVec 64} {need : Nat} {c : BitVec 8}
    (hs1 : s.toNat - need + 512 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h10 : R 10 = BitVec.zeroExtend 64 c) (h11 : R 11 = 0x8001bb20#64) (h2 : R 2 = s)
    {o : Bool} (hc : ConsoleMt (consoleFlagsV o) Mt)
    (hk : ∀ R' M', RetOK R R' (BitVec.zeroExtend 64 c &&& 255#64) → MemKeep Mt M' (outKeep s 512) →
      OutDone M' c → SWPO live (stdioText ++ dataOf impDt (accAddrs 0x8001b970 8)) iRegs (outS s need) Q (t ++ putcs [c]) ra R' M') :
    SWPO live (stdioText ++ dataOf impDt (accAddrs 0x8001b970 8)) iRegs (outS s need) Q t 0x800062e0#64 R Mt := by
  refine fputc_chain hlive hs1 hs3 hs4 hal hra h1 h10 h11 h2 hc ?_
  intros
  have hK : MemKeep _ _ _ := ‹MemKeep _ _ _›
  have hD : OutDone _ c := ‹OutDone _ c›
  refine hk _ _ (retOK_of (by simp [upd_apply]) (by ret_keep)) ⟨fun a ha => ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩
  · have ha' := ha
    simp only [outKeep] at ha'
    simp (disch := nx_addr) only [imgM_store_miss]
    have hk' : outKeep (s + 18446744073709551536#64) 256 a :=
      outKeep_sub (k := 80) (by decide) (by omega) (by decide) ha
    rw [hK.keep a hk']
    simp (disch := nx_addr) only [imgM_store_miss]
  all_goals try (nx_mem; first | exact hD.p | exact hD.w | exact hD.flagsU | exact hD.flagsS)
  simp (disch := nx_addr) only [imgM_store_miss]
  exact hD.buf

end VsaIris.Sym

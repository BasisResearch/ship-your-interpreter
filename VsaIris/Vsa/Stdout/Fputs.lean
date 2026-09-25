import VsaIris.Vsa.Stdout.Fwrite
import VsaIris.Vsa.Stdout.Strlen

/-!
# `fputs(str, stdout)` as a symbolic run (lane N1)

From the boundary state (`ConsoleMt`): `fputs` calls `_fputs_r`, which
measures the string (`strlen`, spliced by `swpo_strlen`), builds a one-iov
`uio` on its frame, takes the (no-op) lock and calls `__sfvwrite_r`
(`sfvwrite_run`), which prints the bytes; it releases the lock and returns
`0`.
-/

namespace VsaIris.Sym

open scoped VsaIris.Sym.Stdout

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.Inst

#ix_seg fputs_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DAs : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s ra P : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    {bv : Nat → BitVec 8}
    (hs1 : s.toNat - need + 512 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (hn1 : bs.length ≤ 0x7ffffc00)
    (h1 : R 1 = ra) (h10 : R 10 = P) (h11 : R 11 = 0x8001bb20#64) (h2 : R 2 = s)
    (hc : ConsoleMt Mt) (hImp : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (c : StrLeaf.LCtx live P 0x800063dc#64 bs.length bv)
    (hD : ∀ q ∈ Strlen.strText P.toNat bs.length bv, q ∈ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs))
    (hb1 : 0x80000000 ≤ P.toNat) (hb2 : P.toNat + bs.length ≤ 0x100000000)
    (hb3 : P.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ P.toNat)
    (hbo : ∀ i, i < bs.length → ¬ outS s need (P.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), P.toNat + i ∈ accAddrs 0x8001b970 8 ++ DAs ∧
      imgM Dt (P.toNat + i) = bs[i]) :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs)) iRegs (outS s need) Q t
      0x80006500#64 R Mt
  by nx_run hlive using [h1, h10, h11, h2, hImp, BitVec.add_assoc] at 2147511536

#ix_piece fputs_B from fputs_A by
  refine swpo_strlen c (by simp [upd_apply]) (by simp [upd_apply]) hD (fun v11 v12 v13 v14 v15 v16 => ?_)

#ix_piece fputs_C from fputs_B by
  nx_run hlive using [h1, BitVec.add_assoc] at 2147540620

#ix_piece fputs_D from fputs_C by
  refine sfvwrite_run (sp := s + 18446744073709551536#64) (ra := 0x8000644c#64)
    (u := s + 18446744073709551560#64) (v := s + 18446744073709551544#64) (buf := P.toNat) (bs := bs)
    hlive ?_ ?_ hs3 hs4 ?_ (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hn1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hb1 hb2 hb3 hbo hsrc (fun R' M' hR hK hF hFu => ?_)
  all_goals try (nx_norm; done)
  all_goals try nx_addr
  all_goals try ((try nx_norm); (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); nx_mem; (try nx_console); (try simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]); done)

#ix_piece fputs_E from fputs_D by
  nx_ret hR
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, h1, hFu, BitVec.add_assoc]

#nx_chain fputs_chain := [fputs_A, fputs_B, fputs_C, fputs_D, fputs_E]

/-- `fputs`'s keep set inside `__sfvwrite_r`'s (its `uio` at `s - 56`). -/
theorem dataKeep_sfv_fputs {s : BitVec 64} {a : Nat} (hs : 512 ≤ s.toNat) (h : dataKeep s 512 a) :
    sfvKeep (s + 18446744073709551536#64) 256 a ∧
      ¬ ((s + 18446744073709551560#64).toNat + 16 ≤ a ∧ a < (s + 18446744073709551560#64).toNat + 24) := by
  simp only [dataKeep, sfvKeep] at *
  nx_addr

/-- **`fputs(str, stdout)`** of a C string (persistent data after
`_impure_ptr`) from the boundary state: prints it, returns `0`; the memory
keeps `dataKeep s 512` and `stdout`'s flags are back. -/
theorem fputs_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DAs : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s ra P : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    {bv : Nat → BitVec 8}
    (hs1 : s.toNat - need + 512 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (hn1 : bs.length ≤ 0x7ffffc00)
    (h1 : R 1 = ra) (h10 : R 10 = P) (h11 : R 11 = 0x8001bb20#64) (h2 : R 2 = s)
    (hc : ConsoleMt Mt) (hImp : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (c : StrLeaf.LCtx live P 0x800063dc#64 bs.length bv)
    (hD : ∀ q ∈ Strlen.strText P.toNat bs.length bv, q ∈ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs))
    (hb1 : 0x80000000 ≤ P.toNat) (hb2 : P.toNat + bs.length ≤ 0x100000000)
    (hb3 : P.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ P.toNat)
    (hbo : ∀ i, i < bs.length → ¬ outS s need (P.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), P.toNat + i ∈ accAddrs 0x8001b970 8 ++ DAs ∧
      imgM Dt (P.toNat + i) = bs[i])
    (hk : ∀ R' M', RetOK R R' 0#64 → MemKeep Mt M' (dataKeep s 512) →
      ldv .lhu M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs)) iRegs (outS s need) Q
        (t ++ putcs bs) ra R' M') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs)) iRegs (outS s need) Q t
      0x80006500#64 R Mt := by
  refine fputs_chain hlive hs1 hs3 hs4 hal hra hn1 h1 h10 h11 h2 hc hImp c hD hb1 hb2 hb3 hbo hsrc ?_
  intros
  have hK : MemKeep _ _ _ := ‹MemKeep _ _ _›
  refine hk _ _ (retOK_of (by simp [upd_apply]) (by ret_keep)) ⟨fun a ha => ?_⟩ ‹_›
  rw [hK.keep a (dataKeep_sfv_fputs (by omega) ha)]
  simp only [dataKeep] at ha
  simp (disch := nx_addr) only [imgM_store_miss]

end VsaIris.Sym

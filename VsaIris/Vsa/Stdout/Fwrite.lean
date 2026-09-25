import VsaIris.Vsa.Stdout.Sfvwrite

/-!
# `fwrite(buf, 1, n, stdout)` as a symbolic run (lane N1)

From the boundary state (`ConsoleMt`): `fwrite` calls `_fwrite_r`, which
computes `n * 1` (`__muldi3`), builds a one-iov `uio` on its frame, takes the
(no-op) lock and calls `__sfvwrite_r` (`sfvwrite_run`), which prints the `n`
bytes; it releases the lock and returns `n`. At `_flags = 0x000a` its
`ORIENT` block runs first; `fwrite_run` takes either orientation, one chain
each (`fwrite_chain`, `fwriteU_chain`) over shared piece scripts.
-/

namespace VsaIris.Sym

open scoped VsaIris.Sym.Stdout

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

set_option hygiene false in
/-- `fwrite` from its entry to `_fwrite_r`'s uio set-up (`0x800050b0`), at
`_flags = fl`. -/
macro "#fwrite_seg " n:ident fl:term : command => `(
  #ix_seg $n {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DAs : List Nat}
      {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
      {R : Nat → BitVec 64} {s ra : BitVec 64} {need : Nat} {buf : Nat} {bs : List (BitVec 8)}
      (hs1 : s.toNat - need + 512 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
      (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
      (hn1 : bs.length ≤ 0x7ffffc00)
      (h1 : R 1 = ra) (h10 : R 10 = BitVec.ofNat 64 buf) (h11 : R 11 = 1#64)
      (h12 : R 12 = BitVec.ofNat 64 bs.length) (h13 : R 13 = 0x8001bb20#64) (h2 : R 2 = s)
      (hc : ConsoleMt $fl Mt) (hImp : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
      (hb1 : 0x80000000 ≤ buf) (hb2 : buf + bs.length ≤ 0x100000000)
      (hb3 : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
      (hbo : ∀ i, i < bs.length → ¬ outS s need (buf + i))
      (hsrc : ∀ i (h : i < bs.length), buf + i ∈ accAddrs 0x8001b970 8 ++ DAs ∧ imgM Dt (buf + i) = bs[i]) :
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs)) iRegs (outS s need) Q t 0x80005260#64 R Mt
    by nx_run hlive using [h1, h10, h11, h12, h13, h2, hImp, BitVec.zero_add, BitVec.add_assoc] at 2147504304)

set_option hygiene false in
/-- `_fwrite_r` to `jal __sfvwrite_r`: the lock and `ORIENT` (from `0x000a`, the
block `0x800050f0`–`0x80005108` stores `_flags2 = 0` and `_flags = 0x200a`). -/
macro "fwrite_A2_tac" : tactic => `(tactic|
  nx_run hlive using [h1, h2, BitVec.zero_add, BitVec.add_assoc] at 2147540620)

set_option hygiene false in
/-- `_fwrite_r`'s call of `__sfvwrite_r` (`sfvwrite_run`). -/
macro "fwrite_B_tac" : tactic => `(tactic| (
    refine sfvwrite_run (sp := s + 18446744073709551504#64) (ra := 0x80005174#64)
      (u := s + 18446744073709551544#64) (v := s + 18446744073709551528#64) (buf := buf) (bs := bs)
      hlive ?_ ?_ hs3 hs4 ?_ (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hn1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hb1 hb2 hb3 hbo hsrc (fun R' M' hR hK hF hFu => ?_)
    all_goals try (nx_norm; done)
    all_goals try nx_addr
    all_goals try ((try nx_norm); (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); nx_mem; (try nx_console); (try nx_norm); done)))

set_option hygiene false in
/-- `_fwrite_r` from `__sfvwrite_r`'s return. -/
macro "fwrite_C_tac" : tactic => `(tactic| (
    nx_ret hR
    nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, h1, hFu, BitVec.add_assoc]))

#fwrite_seg fwrite_A 0x200a#64
#ix_piece fwrite_A2 from fwrite_A by fwrite_A2_tac
#ix_piece fwrite_B from fwrite_A2 by fwrite_B_tac
#ix_piece fwrite_C from fwrite_B by fwrite_C_tac
#nx_chain fwrite_chain := [fwrite_A, fwrite_A2, fwrite_B, fwrite_C]

#fwrite_seg fwriteU_A 0x000a#64
#ix_piece fwriteU_A2 from fwriteU_A by fwrite_A2_tac
#ix_piece fwriteU_B from fwriteU_A2 by fwrite_B_tac
#ix_piece fwriteU_C from fwriteU_B by fwrite_C_tac
#nx_chain fwriteU_chain := [fwriteU_A, fwriteU_A2, fwriteU_B, fwriteU_C]

/-- The bytes a stdout write of persistent data leaves alone: all but its
frames (the `n` bytes below `sp`), `errno` and `stdout`'s flags. -/
@[nx_mt] def dataKeep (sp : BitVec 64) (n : Nat) (a : Nat) : Prop :=
  ¬ (sp.toNat - n ≤ a ∧ a < sp.toNat) ∧ ¬ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∧
    ¬ (0x8001bb30 ≤ a ∧ a < 0x8001bb32)

/-- `fwrite`'s keep set inside `__sfvwrite_r`'s (its `uio` at `s - 72`). -/
theorem dataKeep_sfv {s : BitVec 64} {a : Nat} (hs : 512 ≤ s.toNat) (h : dataKeep s 512 a) :
    sfvKeep (s + 18446744073709551504#64) 256 a ∧
      ¬ ((s + 18446744073709551544#64).toNat + 16 ≤ a ∧ a < (s + 18446744073709551544#64).toNat + 24) := by
  simp only [dataKeep, sfvKeep] at *
  nx_addr

set_option hygiene false in
/-- A `dataKeep` write's end (`fwrite_run`, `fputs_run`): the continuation
`hk` from the chain's end state, the kept bytes through `__sfvwrite_r`'s
frame (`sub`) and the run's own stores (`nx_keep_orient h0`). -/
macro "data_keep_tail " hk:term:max sub:term:max h0:term:max : tactic => `(tactic| (
    intros
    have hK : MemKeep _ _ _ := ‹MemKeep _ _ _›
    refine $hk _ _ (retOK_of (by simp [upd_apply]) (by ret_keep)) ⟨fun a ha => ?_⟩ ‹_›
    rw [hK.keep a ($sub (by omega) ha)]
    simp only [dataKeep] at ha
    nx_keep_orient $h0))

set_option hygiene false in
/-- `fwrite_run` at one orientation (`_flags = fl`), from its chain: each
orientation is its own declaration (its own elaboration budget). -/
macro "#fwrite_run_at " n:ident ch:ident fl:term : command => `(
  theorem $n {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DAs : List Nat}
      {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
      {R : Nat → BitVec 64} {s ra : BitVec 64} {need : Nat} {buf : Nat} {bs : List (BitVec 8)}
      (hs1 : s.toNat - need + 512 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
      (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
      (hn1 : bs.length ≤ 0x7ffffc00)
      (h1 : R 1 = ra) (h10 : R 10 = BitVec.ofNat 64 buf) (h11 : R 11 = 1#64)
      (h12 : R 12 = BitVec.ofNat 64 bs.length) (h13 : R 13 = 0x8001bb20#64) (h2 : R 2 = s)
      (hc : ConsoleMt $fl Mt) (hImp : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
      (hb1 : 0x80000000 ≤ buf) (hb2 : buf + bs.length ≤ 0x100000000)
      (hb3 : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
      (hbo : ∀ i, i < bs.length → ¬ outS s need (buf + i))
      (hsrc : ∀ i (h : i < bs.length), buf + i ∈ accAddrs 0x8001b970 8 ++ DAs ∧ imgM Dt (buf + i) = bs[i])
      (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 bs.length) → MemKeep Mt M' (dataKeep s 512) →
        ldv .lhu M' 0x8001bb30 = 0x200a#64 →
        SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs)) iRegs (outS s need) Q
          (t ++ putcs bs) ra R' M') :
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs)) iRegs (outS s need) Q t
        0x80005260#64 R Mt := by
    refine $ch hlive hs1 hs3 hs4 hal hra hn1 h1 h10 h11 h12 h13 h2 hc hImp hb1 hb2 hb3 hbo hsrc ?_
    data_keep_tail hk dataKeep_sfv hc.lockMode)

#fwrite_run_at fwriteU_run fwriteU_chain 0x000a#64
#fwrite_run_at fwriteO_run fwrite_chain 0x200a#64

/-- **`fwrite(buf, 1, n, stdout)`** of `n` bytes of persistent data (the view
after `_impure_ptr`) from the boundary state: prints them, returns `n`; the
memory keeps `dataKeep s 512` and `stdout`'s flags are back. -/
theorem fwrite_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DAs : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s ra : BitVec 64} {need : Nat} {buf : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 512 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (hn1 : bs.length ≤ 0x7ffffc00)
    (h1 : R 1 = ra) (h10 : R 10 = BitVec.ofNat 64 buf) (h11 : R 11 = 1#64)
    (h12 : R 12 = BitVec.ofNat 64 bs.length) (h13 : R 13 = 0x8001bb20#64) (h2 : R 2 = s)
    {o : Bool} (hc : ConsoleMt (consoleFlagsV o) Mt) (hImp : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (hb1 : 0x80000000 ≤ buf) (hb2 : buf + bs.length ≤ 0x100000000)
    (hb3 : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hbo : ∀ i, i < bs.length → ¬ outS s need (buf + i))
    (hsrc : ∀ i (h : i < bs.length), buf + i ∈ accAddrs 0x8001b970 8 ++ DAs ∧ imgM Dt (buf + i) = bs[i])
    (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 bs.length) → MemKeep Mt M' (dataKeep s 512) →
      ldv .lhu M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs)) iRegs (outS s need) Q
        (t ++ putcs bs) ra R' M') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DAs)) iRegs (outS s need) Q t
      0x80005260#64 R Mt := by
  cases o
  · exact fwriteU_run hlive hs1 hs3 hs4 hal hra hn1 h1 h10 h11 h12 h13 h2 hc hImp hb1 hb2 hb3 hbo hsrc hk
  · exact fwriteO_run hlive hs1 hs3 hs4 hal hra hn1 h1 h10 h11 h12 h13 h2 hc hImp hb1 hb2 hb3 hbo hsrc hk

end VsaIris.Sym

import VsaIris.Interp.SpecStringify
import VsaIris.Interp.CallRegs
import VsaIris.Interp.ProofNativeAssert

/-!
# `stringify` (lane H2)

One run per arm from the kind dispatch to the arm's first call (or, for the
inline arms, to the shared `jal strlen`), then the shared tail: `strlen` of
the buffer (`strlen_specOwnedW`), `malloc` (H1's `mallocRho_spec`), the
out-of-memory block (H5's `wp_oomBlock`) or `memcpy`, the epilogue.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- A run's bytes: the 112-byte frame and the value's slot. -/
abbrev sgF (s p : BitVec 64) (k : Nat) : Prop :=
  InExt (s.toNat - 112, 112) k ∨ InExt (p.toNat, 24) k

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, sgF, VsaIris.InExt] at *; sx_addr))

/-! ## The runs -/

/- `null`: `"null"` stored inline, to `jal strlen`. -/
#ix_seg sg_null {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s p r : BitVec 64}
    (h10 : rv 10 = p) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hk : ldv .lw M p.toNat = 0#64) :
    IW live ∅ [] (sgF s p) Q stringifyPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    unfold stringifyPC
    ix_run1 hlive using [h10, h2, hsf, hk] at 0x80003048

/- `bool`: the constant for `strcpy`, to `jal strcpy`. -/
#ix_seg sg_bool {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s p r bw : BitVec 64}
    (h10 : rv 10 = p) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hk : ldv .lw M p.toNat = 1#64)
    (hb : ldv .lw M (p + 8#64).toNat = bw) :
    IW live ∅ [] (sgF s p) Q stringifyPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    have hp8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    unfold stringifyPC
    ix_run1 hlive using [h10, h2, hsf, hk, hp8, hb] at 0x8000300c
    all_goals (intro _; ix_run1 hlive using [h10, h2, hsf, hk, hp8, hb] at 0x8000300c)

/- `int`: `snprintf(buf, 64, "%lld", i)`, to the `jal`. -/
#ix_seg sg_int {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s p r iw : BitVec 64}
    (h10 : rv 10 = p) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hk : ldv .lw M p.toNat = 2#64)
    (hi : ldv .ld M (p + 8#64).toNat = iw) :
    IW live ∅ [] (sgF s p) Q stringifyPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    have hp8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    unfold stringifyPC
    ix_run1 hlive using [h10, h2, hsf, hk, hp8, hi] at 0x800030d8

/- A string: `strlen` of its payload, to the `jal`. -/
#ix_seg sg_str {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s p r sw : BitVec 64}
    (h10 : rv 10 = p) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hk : ldv .lw M p.toNat = 3#64)
    (hs : ldv .ld M (p + 8#64).toNat = sw) :
    IW live ∅ [] (sgF s p) Q stringifyPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    have hp8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    unfold stringifyPC
    ix_run1 hlive using [h10, h2, hsf, hk, hp8, hs] at 0x800030ec

/- A native: `"<native fn>"` from `.rodata`, to `jal strlen`. -/
#ix_seg sg_nat {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s p r : BitVec 64}
    (h10 : rv 10 = p) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hk : ldv .lw M p.toNat = 5#64) :
    IW live ∅ [] (sgF s p) Q stringifyPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    have hp8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    unfold stringifyPC
    ix_run1 hlive using [h10, h2, hsf, hk] at 0x80003048

/- After `strcpy`: to `jal strlen`. -/
#ix_seg sg_back {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000) :
    IW live ∅ [] (sgF s p) Q 0x80003010#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf] at 0x80003048

/- After `snprintf("%lld")`: to `jal strlen`. -/
#ix_seg sg_backInt {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000) :
    IW live ∅ [] (sgF s p) Q 0x800030dc#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf] at 0x80003048

/- After `snprintf("<fn %s>")`: to `jal strlen`. -/
#ix_seg sg_backFn {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000) :
    IW live ∅ [] (sgF s p) Q 0x80003044#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf] at 0x80003048

/- After `strlen` of the buffer: `malloc(len + 1)`. -/
#ix_seg sg_len {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000) :
    IW live ∅ [] (sgF s p) Q 0x8000304c#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf] at 0x80003058

/- `malloc` returned NULL: to the out-of-memory block. -/
#ix_seg sg_oom {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (h10 : R 10 = 0#64) :
    IW live ∅ [] (sgF s p) Q 0x8000305c#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf, h10] at 0x80003140
    all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; exact h10)
      | skip

/- `malloc` returned a block: `memcpy(block, buf, len + 1)`. -/
#ix_seg sg_copy {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (h10 : R 10 ≠ 0#64) :
    IW live ∅ [] (sgF s p) Q 0x8000305c#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf] at 0x8000306c

/- The epilogue after `memcpy`. -/
#ix_seg sg_epi {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p r v8 v9 : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hal : r.toNat % 4 = 0)
    (hra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r)
    (hs0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = v8)
    (hs1' : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = v9) :
    IW live ∅ [] (sgF s p) Q 0x80003070#64 R M
  by
    ix_run1 hlive using [h2, hal, hra, hs0, hs1']

/- After `strlen` of a string: `malloc(len + 1)`. -/
#ix_seg sg_slen {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000) :
    IW live ∅ [] (sgF s p) Q 0x800030f0#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf] at 0x800030f8

/- `malloc` returned NULL (string arm): to the out-of-memory block. -/
#ix_seg sg_soom {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (h10 : R 10 = 0#64) :
    IW live ∅ [] (sgF s p) Q 0x800030fc#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf, h10] at 0x80003140
    all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; exact h10)
      | skip

/- `malloc` returned a block (string arm): `memcpy`. -/
#ix_seg sg_scopy {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (h10 : R 10 ≠ 0#64) :
    IW live ∅ [] (sgF s p) Q 0x800030fc#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf] at 0x8000310c

/- The epilogue after `memcpy` (string arm). -/
#ix_seg sg_sepi {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s p r v8 v9 : BitVec 64}
    (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hal : r.toNat % 4 = 0)
    (hra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r)
    (hs0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = v8)
    (hs1' : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = v9) :
    IW live ∅ [] (sgF s p) Q 0x80003110#64 R M
  by
    ix_run1 hlive using [h2, hal, hra, hs0, hs1']


end VsaIris.Interp

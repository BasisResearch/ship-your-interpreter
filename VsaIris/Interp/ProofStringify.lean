import VsaIris.Interp.SpecStringify
import VsaIris.Interp.CallMalloc
import VsaIris.Interp.ProofNativeAssert
import VsaIris.Vsa.StrlenOwned
import VsaIris.Vsa.OomSites
import VsaIris.Vsa.SnpHoles

/-!
# `stringify` (lane H2)

One run per arm from the kind dispatch to the arm's first call (or, for the
inline arms, to the shared `jal strlen`), then the shared tail: `strlen` of
the buffer (`strlen_specOwnedW`), `malloc` (H1's `mallocRho_spec`), the
out-of-memory block (H5's `wp_oomBlock`) or `memcpy`, the epilogue.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.Stdio VsaIris.VsaHeap
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


/- A closure: the prologue and the kind dispatch, to its arm (`0x8000301c`). -/
#ix_seg sg_cloH {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s p r : BitVec 64}
    (h10 : rv 10 = p) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hk : ldv .lw M p.toNat = 4#64) :
    IW live ∅ [] (sgF s p) Q stringifyPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    unfold stringifyPC
    ix_run1 hlive using [h10, h2, hsf, hk] at 0x8000301c

/- A closure, named: its object's `EX_FN` node's name field (the data view), to
`jal snprintf`. -/
#ix_seg sg_cloN {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M Dt : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64} {cp q nm : Nat}
    (h10 : R 10 = p) (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hw8 : ldv .ld M (p + 8#64).toNat = BitVec.ofNat 64 cp)
    (hc0 : ReadOK cp) (hc7 : ReadOK (cp + 7)) (hq : ldv .ld Dt cp = BitVec.ofNat 64 q)
    (hq0 : ReadOK (q + 8)) (hq7 : ReadOK (q + 15)) (hnm : ldv .ld Dt (q + 8) = BitVec.ofNat 64 nm)
    (hnz : BitVec.ofNat 64 nm ≠ 0#64) (hcp : cp < 2 ^ 64) (hql : q + 8 < 2 ^ 64) :
    IW live Dt (clodA cp q) (sgF s p) Q 0x8000301c#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    have c1 := hc0.lo; have c2 := hc0.hi; have c3 := hc0.off
    have c4 := hc7.lo; have c5 := hc7.hi; have c6 := hc7.off
    have q1 := hq0.lo; have q2 := hq0.hi; have q3 := hq0.off
    have q4 := hq7.lo; have q5 := hq7.hi; have q6 := hq7.off
    have ecp : (BitVec.ofNat 64 cp).toNat = cp := by simp; omega
    have eq8 : (BitVec.ofNat 64 q + 8#64).toNat = q + 8 := by rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h10, h2, hsf, hw8, ecp, hq, eq8, hnm, hnz] at 0x80003040

/- A closure, anonymous: `"<fn>"` stored inline, to `jal strlen`. -/
#ix_seg sg_cloA {live : Nat → Prop} (hlive : ∀ q ∈ interpText, live q.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M Dt : Mem} {R : Nat → BitVec 64}
    {s p : BitVec 64} {cp q : Nat}
    (h10 : R 10 = p) (h2 : R 2 = s + 18446744073709551504#64)
    (hs1 : 0x87800000 + 112 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hp1 : p.toNat % 8 = 0) (hp2 : 0x8001ad00 + 16 ≤ p.toNat) (hp3 : p.toNat + 24 ≤ 0x100000000)
    (hw8 : ldv .ld M (p + 8#64).toNat = BitVec.ofNat 64 cp)
    (hc0 : ReadOK cp) (hc7 : ReadOK (cp + 7)) (hq : ldv .ld Dt cp = BitVec.ofNat 64 q)
    (hq0 : ReadOK (q + 8)) (hq7 : ReadOK (q + 15)) (hnm : ldv .ld Dt (q + 8) = 0#64)
    (hcp : cp < 2 ^ 64) (hql : q + 8 < 2 ^ 64) :
    IW live Dt (clodA cp q) (sgF s p) Q 0x8000301c#64 R M
  by
    have hsf : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
      rw [BitVec.toNat_add]; simp; omega
    have c1 := hc0.lo; have c2 := hc0.hi; have c3 := hc0.off
    have c4 := hc7.lo; have c5 := hc7.hi; have c6 := hc7.off
    have q1 := hq0.lo; have q2 := hq0.hi; have q3 := hq0.off
    have q4 := hq7.lo; have q5 := hq7.hi; have q6 := hq7.off
    have ecp : (BitVec.ofNat 64 cp).toNat = cp := by simp; omega
    have eq8 : (BitVec.ofNat 64 q + 8#64).toNat = q + 8 := by rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h10, h2, hsf, hw8, ecp, hq, eq8, hnm] at 0x80003048

/-! ## Bytes a run's stores leave -/

theorem imgM_sw (Mt : Mem) (a : Nat) (v : BitVec 64) (i : Nat) (hi : i < 4) :
    imgM (writeLog Mt [(a, 4, v)]) (a + i) = (swData v).extractLsb' (8 * i) 8 := by
  unfold imgM writeLog
  simp only [List.foldl, applyW, writeMap4, Std.ExtHashMap.getElem?_insert]
  rcases i with _ | _ | _ | _ | i
  all_goals first
    | omega
    | simp

theorem imgM_sb (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgM (writeLog Mt [(a, 1, v)]) a = sbData v := by
  unfold imgM writeLog
  simp only [List.foldl, applyW, Std.ExtHashMap.getElem?_insert]
  simp

theorem imgM_sd (Mt : Mem) (a : Nat) (v : BitVec 64) (i : Nat) (hi : i < 8) :
    imgM (writeLog Mt [(a, 8, v)]) (a + i) = (sdData_val v).extractLsb' (8 * i) 8 := by
  unfold imgM writeLog
  simp only [List.foldl, applyW, writeMap8, Std.ExtHashMap.getElem?_insert]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first
    | omega
    | simp

/-- `"null"` as the `null` arm stores it: one word and a NUL. -/
theorem cstr_null (Mt : Mem) (a : Nat) :
    CStrImg (imgM (writeLog (writeLog Mt [(a, 4, 1819047278#64)]) [(a + 4, 1, 0#64)])) a "null" := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have hi' : i < 4 := by simpa using hi
    rw [imgM_store_miss _ _ (by omega), imgM_sw _ _ _ _ hi']
    rcases i with _ | _ | _ | _ | i
    all_goals first | omega | (revert hi hi'; decide)
  · rw [show a + "null".toList.length = a + 4 from rfl, imgM_sb]; decide

/-- `"<native fn>"` as the native arm stores it: two `.rodata` words. -/
theorem cstr_native (Mt : Mem) (a : Nat) :
    CStrImg (imgM (writeLog (writeLog Mt [(a, 8, 2334402177157656124#64)])
      [(a + 8, 4, 4091494#64)])) a "<native fn>" := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have hi' : i < 11 := by simpa using hi
    by_cases h8 : i < 8
    · rw [imgM_store_miss _ _ (by omega), imgM_sd _ _ _ _ h8]
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first | omega | (revert hi hi' h8; decide)
    · have := imgM_sw (writeLog Mt [(a, 8, 2334402177157656124#64)]) (a + 8) 4091494#64 (i - 8)
        (by omega)
      rw [show a + 8 + (i - 8) = a + i by omega] at this
      rw [this]
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first | omega | (revert hi hi' h8; decide)
  · have := imgM_sw (writeLog Mt [(a, 8, 2334402177157656124#64)]) (a + 8) 4091494#64 3 (by omega)
    rw [show a + "<native fn>".toList.length = a + 8 + 3 from rfl, this]; decide

/-! ## The length of a 64-bit integer's rendering -/

theorem natDigits_len : ∀ (fuel n k : Nat), n < 10 ^ k → 1 ≤ k → (natDigits fuel n).length ≤ k
  | 0, _, _, _, _ => by simp [natDigits]
  | fuel + 1, n, k, hn, hk => by
    unfold natDigits
    by_cases h : n < 10
    · simp only [h, ite_true, List.length_singleton]; exact hk
    · simp only [h, ite_false, List.length_append, List.length_singleton]
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have : k = 1 := by omega
          subst this; simp at hn; omega
        · exact hk2
      have hpow : 10 ^ k = 10 * 10 ^ (k - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have := natDigits_len fuel (n / 10) (k - 1)
        (by rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [hpow] at hn; rw [Nat.mul_comm]; exact hn)
        (by omega)
      omega

theorem natToString_toList' (n : Nat) : (natToString n).toList = natDigits (n + 1) n := by
  unfold natToString
  suffices h : ∀ (l : List Char) (s : String), (l.foldl String.push s).toList = s.toList ++ l by
    rw [h]; simp
  intro l
  induction l with
  | nil => intro s; simp
  | cons c t ih => intro s; rw [List.foldl_cons, ih, String.toList_push]; simp

/-- A 64-bit integer renders in at most 20 characters. -/
theorem intToString_len_le (i : Int) (h1 : -(2 ^ 63) ≤ i) (h2 : i < 2 ^ 63) :
    (intToString i).toList.length ≤ 20 := by
  cases i with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast] at h2
    simp only [intToString, natToString_toList']
    have := natDigits_len (m + 1) m 19 (by omega) (by decide)
    omega
  | negSucc m =>
    simp only [Int.negSucc_eq] at h1
    simp only [intToString, String.toList_append, List.length_append, natToString_toList']
    have := natDigits_len (m + 1 + 1) (m + 1) 19 (by omega) (by decide)
    simp; omega

/-- `"<fn>"` as the anonymous-closure arm stores it: one word and a NUL. -/
theorem cstr_fn (Mt : Mem) (a : Nat) :
    CStrImg (imgM (writeLog (writeLog Mt [(a, 4, 1047422524#64)]) [(a + 4, 1, 0#64)])) a "<fn>" := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have hi' : i < 4 := by simpa using hi
    rw [imgM_store_miss _ _ (by omega), imgM_sw _ _ _ _ hi']
    rcases i with _ | _ | _ | _ | i
    all_goals first | omega | (revert hi hi'; decide)
  · rw [show a + "<fn>".toList.length = a + 4 from rfl, imgM_sb]; decide

/-! ## The Iris glue -/

section Glue

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- `stringify`'s continuation pair (its `fnSpecAbort` post and abort), at
the rendering `x`. -/
abbrev SgK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (inp : Nat) (p s r : BitVec 64) (v : Value) (x : String) (ρ : Regime)
    (H : List (Nat × Nat)) (o : String) (rv : Nat → BitVec 64) : IProp GF :=
  iprop((PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
      (∃ (rv' : Nat → BitVec 64) (q : BitVec 64), regFile rv' ∗
        ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗ ⌜rv' 10 = q⌝ ∗
        valAt N p.toNat v ∗ strOwn q.toNat x ∗
        ⌜FreshBlock vsaLayoutP H q.toNat (x.toList.length + 1) ∧ q.toNat % 16 = 0⌝ ∗
        heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, x.toList.length + 1) :: H) ∗
        stdioOwn ∗ consoleOwn o ∗ stackAt s stringifyNeed) -∗ Wp.W Φ) ∧
    (iprop(⌜ρ = .uncounted⌝ ∗ abortRes N vsaLayoutP vsaRoomB inp s stringifyNeed ∗
      slot24 p.toNat) -∗ Wp.W Φ))

/-- What a `stringify` run carries: the value's meaning at its image, the heap,
newlib's data and the console, the stack below the frame, the continuation. -/
def SgRest (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (inp : Nat) (p s r : BitVec 64) (v : Value) (x : String) (ρ : Regime)
    (H : List (Nat × Nat)) (c : Nat) (o : String) (rv : Nat → BitVec 64) (Mp : Mem) : IProp GF :=
  iprop(codeRes ∗ binImg ∗ textOwn allocText ∗ valImg N (imgM Mp) p.toNat v ∗
    heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗ stdioOwn ∗ consoleOwn o ∗
    stackScratch (s + 18446744073709551504#64) (stringifyNeed - 112) ∗
    SgK Wp Φ N inp p s r v x ρ H o rv)

/-- The shared pure facts of a `stringify` run. -/
structure SgCtx (live : Nat → Prop) (p s r : BitVec 64) (rv : Nat → BitVec 64) : Prop where
  hlive : ∀ q ∈ interpText, live q.1
  hcl : CodeLive live
  hstk : ∀ a, 0x87800000 ≤ a → a < 0x88000000 → live a
  hal : r.toNat % 4 = 0
  h10 : rv 10 = p
  h2 : rv 2 = s
  hs1 : 0x87800000 + stringifyNeed ≤ s.toNat
  hs2 : s.toNat ≤ 0x88000000
  hs3 : s.toNat % 16 = 0
  hs4 : s.toNat ≤ Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame
  hg : SlotGeom p
  hdsp : ∀ k, InExt (s.toNat - 112, 112) k → ¬ InExt (p.toNat, 24) k

/-- The frame and the value's slot are apart, numerically. -/
theorem SgCtx.sep {live : Nat → Prop} {p s r : BitVec 64} {rv : Nat → BitVec 64}
    (cx : SgCtx live p s r rv) : p.toNat + 24 ≤ s.toNat - 112 ∨ s.toNat ≤ p.toNat := by
  have hs1 := cx.hs1
  unfold stringifyNeed snprintfNeed at hs1
  by_cases h1 : p.toNat + 24 ≤ s.toNat - 112
  · exact .inl h1
  by_cases h2 : s.toNat ≤ p.toNat
  · exact .inr h2
  exfalso
  by_cases h3 : p.toNat ≤ s.toNat - 112
  · exact cx.hdsp (s.toNat - 112) (by simp only [InExt]; omega) (by simp only [InExt]; omega)
  · exact cx.hdsp p.toNat (by simp only [InExt]; omega) (by simp only [InExt]; omega)

/-- At `jal strlen` (`0x80003048`): the rendering `x` in the buffer
`sp + 16`, which `s1` and `a0` point at. -/
structure SgT1 (s p r : BitVec 64) (x : String) (rv R : Nat → BitVec 64) (M Mp : Mem) : Prop where
  h10 : R 10 = s + 18446744073709551504#64 + 16#64
  h9 : R 9 = s + 18446744073709551504#64 + 16#64
  h2 : R 2 = s + 18446744073709551504#64
  hk : ∀ y ∈ fRegs, y ∉ callerSaved → y ≠ 2 → y ≠ 9 → R y = rv y
  sra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = rv 9
  hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k
  hbuf : CStrImg (imgM M) (s.toNat - 96) x
  hlen : x.toList.length ≤ 63

/-- At `jal malloc` (`0x80003058`): `len + 1` in `a0` and at `sp + 8`. -/
structure SgT2 (s p r : BitVec 64) (x : String) (rv R : Nat → BitVec 64) (M Mp : Mem) : Prop where
  h10 : R 10 = BitVec.ofNat 64 (x.toList.length + 1)
  h9 : R 9 = s + 18446744073709551504#64 + 16#64
  h2 : R 2 = s + 18446744073709551504#64
  hk : ∀ y ∈ fRegs, y ∉ callerSaved → y ≠ 2 → y ≠ 9 → R y = rv y
  sra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = rv 9
  sn : ldv .ld M (s + 18446744073709551504#64 + 8#64).toNat = BitVec.ofNat 64 (x.toList.length + 1)
  hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k
  hbuf : CStrImg (imgM M) (s.toNat - 96) x
  hlen : x.toList.length ≤ 63

/-- A C string image gives `strlen`'s byte facts. -/
theorem strBytes_of_cstrImg {img : Nat → BitVec 8} {q : Nat} {x : String} (h : CStrImg img q x) :
    Strlen.StrBytes q x.toList.length img where
  nonzero k hk := by
    obtain ⟨e, h1, h2⟩ := h.1 k hk
    rw [e]; intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega
  ascii k hk := by
    obtain ⟨e, h1, h2⟩ := h.1 k hk
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h2
  nul := h.2

/-- A C string's image read through another image agreeing on it. -/
theorem cstrImg_congr {img img' : Nat → BitVec 8} {q : Nat} {x : String} (h : CStrImg img q x)
    (he : ∀ i, i ≤ x.toList.length → img' (q + i) = img (q + i)) : CStrImg img' q x :=
  ⟨fun i hi => by rw [he i (by omega)]; exact h.1 i hi,
    by rw [he _ (Nat.le_refl _)]; exact h.2⟩

/-- **`strlen` of the buffer**, then the run to `jal malloc`. -/
theorem sg_strlen (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (cx : SgCtx live p s r rv) {R : Nat → BitVec 64} {M : Mem} (f : SgT1 s p r x rv R M Mp)
    (hB : ∀ R' M', SgT2 s p r x rv R' M' Mp →
      SgRest Wp Φ N inp p s r v x ρ H c o rv Mp ∗ ms 0x80003058#64 R' (sgF s p) M' ⊢ Wp.W Φ) :
    SgRest Wp Φ N inp p s r v x ρ H c o rv Mp ∗ ms 0x80003048#64 R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hlen := f.hlen
  have eP : (s + 18446744073709551504#64 + 16#64).toNat = s.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have hsub : ∀ k, Strlen.ownedStr (s.toNat - 96) x.toList.length k → sgF s p k := fun k hk =>
    .inl (by unfold Strlen.ownedStr at hk; simp only [InExt]; omega)
  have hsl : ∀ k, sgF s p k ↔ ((sgF s p k ∧ ¬ Strlen.ownedStr (s.toNat - 96) x.toList.length k) ∨
      Strlen.ownedStr (s.toNat - 96) x.toList.length k) := fun k => by
    constructor
    · intro h; by_cases h' : Strlen.ownedStr (s.toNat - 96) x.toList.length k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hsub k h
  have hreg : Strlen.ReadRegions (s + 18446744073709551504#64 + 16#64) x.toList.length := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [eP] <;> first | omega | (unfold Vsa.Sim.tohostAddr; omega)
  have hlv : ∀ k, k < x.toList.length + 8 →
      live ((s + 18446744073709551504#64 + 16#64).toNat + k) := fun k hk =>
    cx.hstk _ (by rw [eP]; omega) (by rw [eP]; omega)
  iintro ⟨Hrest, Hms⟩
  ihave Hms := ms_iff hsl $$ Hms
  ihave ⟨Hms, HB⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  unfold SgRest
  icases Hrest with ⟨#Hcode, #Himg, #Hat, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
  ihave #Hsl := Strlen.strlenOwned_fn live cx.hcl Wp (bv := imgM M) hreg
    (by rw [eP]; exact strBytes_of_cstrImg f.hbuf) hlv $$ Himg
  rw [eP]
  iapply (ms_callRegs Wp (i := 0x80003048)
    (jalx_80003048 live (fun q hq => cx.hlive _ (interp_code_80003048 q hq))) interp_code_80003048
    (L := [10, 11, 12, 13, 14, 15])
    (K := [2, 5, 6, 7, 8, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])
    (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ (s + 18446744073709551504#64 + 16#64) ∗
      clobbered [11, 12, 13, 14, 15] ∗
      ownSet (Strlen.ownedStr (s.toNat - 96) x.toList.length) (fun a => a ↦ₘ imgM M a)))
    (Q := fun _ => iprop((10 : Nat) ↦ᵣ BitVec.ofNat 64 x.toList.length ∗
      clobbered [11, 12, 13, 14, 15] ∗
      ownSet (Strlen.ownedStr (s.toNat - 96) x.toList.length) (fun a => a ↦ₘ imgM M a)))
    (X := ownSet (Strlen.ownedStr (s.toNat - 96) x.toList.length) (fun a => a ↦ₘ imgM M a))
    (Y := fun g => iprop(⌜g 10 = BitVec.ofNat 64 x.toList.length⌝ ∗
      ownSet (Strlen.ownedStr (s.toNat - 96) x.toList.length) (fun a => a ↦ₘ imgM M a)))
    (R := R) (Mt := M) ?hP ?hQ)
  case hP =>
    simp only [sepL_cons, sepL_nil]
    iintro ⟨⟨H10, H11, H12, H13, H14, H15, -⟩, HB⟩
    rw [f.h10]
    iframe H10 HB
    isplitl []
    · ipureintro; decide
    iapply clobbered_of_fn [11, 12, 13, 14, 15] R
    simp only [sepL_cons, sepL_nil]
    iframe H11 H12 H13 H14 H15
  case hQ =>
    iintro ⟨H10, Hcl, HB⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn [11, 12, 13, 14, 15] (by decide) $$ Hcl
    iexists (fun y => if y = 10 then BitVec.ofNat 64 x.toList.length else g y)
    simp only [sepL_cons, sepL_nil]
    icases Hcl with ⟨H11, H12, H13, H14, H15, -⟩
    simp only [ite_true, show (11 : Nat) ≠ 10 from by decide, show (12 : Nat) ≠ 10 from by decide,
      show (13 : Nat) ≠ 10 from by decide, show (14 : Nat) ≠ 10 from by decide,
      show (15 : Nat) ≠ 10 from by decide, ite_false]
    iframe H10 H11 H12 H13 H14 H15 HB
  iframe Hsl Hcode Hms HB
  iintro %g ⟨%hg10, HB⟩ Hms
  ihave ⟨%M1, Hms, %⟨hM1a, hM1b, -⟩⟩ := ms_join $$ [Hms HB]
  · iframe Hms HB
  ihave Hms := ms_iff (fun k => (hsl k).symm) $$ Hms
  have hM1 : ∀ k, sgF s p k → imgM M1 k = imgM M k := fun k hk => by
    by_cases h : Strlen.ownedStr (s.toNat - 96) x.toList.length k
    · exact hM1b k h
    · exact hM1a k ⟨hk, h⟩
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  iapply wp_swpF Wp (S := sgF s p)
    (R := upd (fun y => if y ∈ [10, 11, 12, 13, 14, 15] then g y else R y) 1
      (BitVec.ofNat 64 (0x80003048 + 4))) (Mt := M1) (pc := 0x8000304c#64)
    (F := SgRest Wp Φ N inp p s r v x ρ H c o rv Mp)
  rotate_left
  · rw [hro]; unfold SgRest
    iframe Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms
  intro F'
  refine sg_len cx.hlive (by ix_reg; exact f.h2) (by omega) hs2 hs3 cx.hg.al
    (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi ?_
  intros; apply swp_closeF
  dsimp only [F']
  iintro ⟨Hrest, Hms⟩
  iapply (hB _ _ ?t2)
  rotate_left
  · iframe Hrest Hms
  case t2 =>
    have hoff : ∀ k, k < 112 → (s + 18446744073709551504#64 + BitVec.ofNat 64 k).toNat =
        s.toNat - 112 + k := by
      intro k hk; rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
    have hg' : g 10 + 1#64 = BitVec.ofNat 64 (x.toList.length + 1) := by
      rw [hg10]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show x.toList.length < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide),
        Nat.mod_eq_of_lt (show x.toList.length + 1 < 2 ^ 64 by omega)]
    have hfr : ∀ (w : BitVec 64) o, 16 ≤ o → o + 8 ≤ 112 → ∀ j, j < 8 →
        imgM (writeLog M1 [((s + 18446744073709551504#64 + 8#64).toNat, 8, w)])
          (s.toNat - 112 + o + j) = imgM M (s.toNat - 112 + o + j) := fun w o h1 h2 j hj => by
      rw [hoff 8 (by omega), imgM_store_miss _ _ (by omega)]
      exact hM1 _ (.inl (by simp only [InExt]; omega))
    have hld : ∀ (w : BitVec 64) o, 16 ≤ o → o + 8 ≤ 112 →
        ldv .ld (writeLog M1 [((s + 18446744073709551504#64 + 8#64).toNat, 8, w)])
          (s + 18446744073709551504#64 + BitVec.ofNat 64 o).toNat =
        ldv .ld M (s + 18446744073709551504#64 + BitVec.ofNat 64 o).toNat := fun w o h1 h2 => by
      rw [hoff o (by omega)]
      exact ldv_agree fun j hj => hfr w o h1 h2 j hj
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, f.hlen⟩
    · ix_reg; exact hg'
    · ix_reg; exact f.h9
    · ix_reg; exact f.h2
    · intro y hy hc hy2 hy9
      have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
      have hL : y ∉ [10, 11, 12, 13, 14, 15] := fun h => hc (by revert h; revert y; decide)
      have hy10 : y ≠ 10 := fun e => hL (by simp [e])
      have hy12 : y ≠ 12 := fun e => hL (by simp [e])
      simp only [upd, hy1, hy10, hy12, hL, ite_false]
      exact f.hk y hy hc hy2 hy9
    · rw [hld _ 104 (by omega) (by omega)]; exact f.sra
    · rw [hld _ 96 (by omega) (by omega)]; exact f.ss0
    · rw [hld _ 88 (by omega) (by omega)]; exact f.ss1
    · rw [ldv_store_hit]; ix_reg; exact hg'
    · intro k hk
      have hk' := cx.hdsp k
      have hnf : ¬ InExt (s.toNat - 112, 112) k := fun h => hk' h hk
      simp only [InExt] at hk hnf
      rw [hoff 8 (by omega), imgM_store_miss _ _ (by omega), hM1 k (.inr (by simp only [InExt]; omega))]
      exact f.hslot k (by simp only [InExt]; omega)
    · exact cstrImg_congr f.hbuf fun i hi => by
        rw [hoff 8 (by omega), imgM_store_miss _ _ (by omega)]
        exact hM1 _ (.inl (by simp only [InExt]; omega))

omit I in
/-- `stringify`'s frame out of the stack below `s`, and back. -/
theorem sgFrame_join {s : BitVec 64} (hs : stringifyNeed ≤ s.toNat) :
    stackScratch (GF := GF) (s + 18446744073709551504#64) (stringifyNeed - 112) ∗
        ownSet (InExt (s.toNat - 112, 112)) byteAny ⊢ stackScratch s stringifyNeed := by
  have h := stackScratch_unframe (GF := GF) (s := s) (f := 112#64) (n := stringifyNeed) hs
    (by unfold stringifyNeed; simp)
  have hsm : s - 112#64 = s + 18446744073709551504#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have e : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
    unfold stringifyNeed at hs; rw [BitVec.toNat_add]; simp; omega
  rw [hsm, e, show (112#64 : BitVec 64).toNat = 112 from rfl] at h
  unfold blockOwn at h
  exact h

omit I in
theorem sgFrame_split {s : BitVec 64} (hs : stringifyNeed ≤ s.toNat) :
    stackScratch (GF := GF) s stringifyNeed ⊢
      stackScratch (s + 18446744073709551504#64) (stringifyNeed - 112) ∗
        ownSet (InExt (s.toNat - 112, 112)) byteAny := by
  have h := stackScratch_frame (GF := GF) (s := s) (f := 112#64) (n := stringifyNeed) hs
    (by unfold stringifyNeed; simp)
  have hsm : s - 112#64 = s + 18446744073709551504#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have e : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
    unfold stringifyNeed at hs; rw [BitVec.toNat_add]; simp; omega
  rw [hsm, e, show (112#64 : BitVec 64).toNat = 112 from rfl] at h
  unfold blockOwn at h
  exact h

/-- The out-of-memory block from any register values (H5's `wp_oomBlock` at
`oom80003140`): the abort branch takes the whole stack region. -/
theorem sg_oomEnd (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (HN : NewlibHoles) (cx : SgCtx live p s r rv) (hρ : ρ = .uncounted) {R : Nat → BitVec 64}
    {M : Mem} (h2 : R 2 = s + 18446744073709551504#64) :
    SgRest Wp Φ N inp p s r v x ρ H c o rv Mp ∗ ms 0x80003140#64 R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have e112 : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
    rw [BitVec.toNat_add]; simp; omega
  unfold SgRest
  iintro ⟨⟨#Hcode, #Himg, -, -, -, Hstd, Hcon, Hst, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave ⟨HF, HP⟩ := ownSet_split _ (InExt (s.toNat - 112, 112)) _ $$ HS
  ihave HF := ownSet_iff _ (fun k => ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩) $$ HF
  ihave HP := ownSet_iff _ (T := InExt (p.toNat, 24)) (fun k =>
    ⟨fun h => h.1.resolve_left h.2, fun h => ⟨.inr h, fun h' => cx.hdsp k h' h⟩⟩) $$ HP
  ihave Hst := sgFrame_join (s := s) (by unfold stringifyNeed snprintfNeed; omega) $$ [Hst HF]
  · iframe Hst HF
  ihave ⟨Hsp, Hcs, Htmp, Hargs⟩ := (regFile_newlib _).1 $$ Hregs
  ihave Htmp := clobbered_of_fn _ _ $$ Htmp
  ihave Hargs := clobbered_of_fn _ _ $$ Hargs
  ihave #Hgp := codeRes_gp $$ Hcode
  ihave Hk := and_elim_r $$ Hk
  rw [h2]
  iapply Oom.wp_oomBlock HN live cx.hcl Wp N vsaLayoutP vsaRoomB inp OomSites.oom80003140
    OomSites.oom80003140_ok s (s + 18446744073709551504#64) _ stringifyNeed
    ⟨by unfold stringifyNeed snprintfNeed; omega,
      by unfold stringifyNeed snprintfNeed Vsa.Sim.tohostAddr; omega,
      by rw [e112]; unfold stringifyNeed snprintfNeed fwriteNeed; omega,
      by rw [e112]; show s.toNat - 112 + 0 ≤ s.toNat; omega, hs2, by rw [e112]; omega⟩ _ o
  rw [show BitVec.ofNat 64 OomSites.oom80003140.head = 2147496256#64 from rfl]
  iframe Hpc Hra Hsp Hargs Htmp Hcs Hgp Himg Hst Hstd Hcon
  iintro HA
  iapply Hk
  isplitl []
  · ipureintro; exact hρ
  iframe HA
  unfold slot24 blockOwn
  iexact HP

/-- **Out of memory**: from `malloc`'s NULL (either copy tail), the run to
the out-of-memory block. -/
theorem sg_oomPath (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (HN : NewlibHoles) (cx : SgCtx live p s r rv) (hρ : ρ = .uncounted) {pc : Nat}
    (hpc : pc = 0x8000305c ∨ pc = 0x800030fc)
    {R : Nat → BitVec 64} {M : Mem}
    (h2 : R 2 = s + 18446744073709551504#64) (h10 : R 10 = 0#64) :
    SgRest Wp Φ N inp p s r v x ρ H c o rv Mp ∗ ms (BitVec.ofNat 64 pc) R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := R) (Mt := M) (pc := BitVec.ofNat 64 pc)
    (F := SgRest Wp Φ N inp p s r v x ρ H c o rv Mp)
  rotate_left
  · unfold SgRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  rcases hpc with rfl | rfl
  · refine sg_oom cx.hlive h2 (by omega) hs2 hs3 cx.hg.al
      (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi h10 ?_
    intros; apply swp_closeF
    dsimp only [F']
    exact sg_oomEnd Wp HN cx hρ (by ix_reg; exact h2)
  · refine sg_soom cx.hlive h2 (by omega) hs2 hs3 cx.hg.al
      (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi h10 ?_
    intros; apply swp_closeF
    dsimp only [F']
    exact sg_oomEnd Wp HN cx hρ (by ix_reg; exact h2)

/-- After `malloc` returned the block `q`: the heap extended, the block owned. -/
def SgRestB (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (inp : Nat) (p s r : BitVec 64) (v : Value) (x : String) (ρ : Regime)
    (H : List (Nat × Nat)) (o : String) (rv : Nat → BitVec 64) (Mp : Mem) (q : BitVec 64) :
    IProp GF :=
  iprop(codeRes ∗ binImg ∗ valImg N (imgM Mp) p.toNat v ∗
    heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, x.toList.length + 1) :: H) ∗
    blockOwn q.toNat (x.toList.length + 1) ∗ stdioOwn ∗ consoleOwn o ∗
    stackScratch (s + 18446744073709551504#64) (stringifyNeed - 112) ∗
    SgK Wp Φ N inp p s r v x ρ H o rv)

/-- After `memcpy`: the block holds the buffer's bytes `img`. -/
def SgRestC (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (inp : Nat) (p s r : BitVec 64) (v : Value) (x : String) (ρ : Regime)
    (H : List (Nat × Nat)) (o : String) (rv : Nat → BitVec 64) (Mp : Mem) (q : BitVec 64)
    (img : Nat → BitVec 8) : IProp GF :=
  iprop(codeRes ∗ valImg N (imgM Mp) p.toNat v ∗
    heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, x.toList.length + 1) :: H) ∗
    ownImg (InExt (q.toNat, x.toList.length + 1)) img ∗ stdioOwn ∗ consoleOwn o ∗
    stackScratch (s + 18446744073709551504#64) (stringifyNeed - 112) ∗
    SgK Wp Φ N inp p s r v x ρ H o rv)

/-- At `malloc`'s return (`0x8000305c`) with the block `q`. -/
structure SgT3 (s p r : BitVec 64) (x : String) (H : List (Nat × Nat)) (q : BitVec 64)
    (rv R : Nat → BitVec 64) (M Mp : Mem) : Prop where
  h10 : R 10 = q
  h9 : R 9 = s + 18446744073709551504#64 + 16#64
  h2 : R 2 = s + 18446744073709551504#64
  hk : ∀ y ∈ fRegs, y ∉ callerSaved → y ≠ 2 → y ≠ 9 → R y = rv y
  sra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = rv 9
  sn : ldv .ld M (s + 18446744073709551504#64 + 8#64).toNat = BitVec.ofNat 64 (x.toList.length + 1)
  hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k
  hbuf : CStrImg (imgM M) (s.toNat - 96) x
  hlen : x.toList.length ≤ 63
  hfresh : FreshBlock vsaLayoutP H q.toNat (x.toList.length + 1) ∧ q.toNat % 16 = 0

/-- After `memcpy` (`0x80003070`): `s0` holds the block, the block holds `img`,
a copy of the rendering. -/
structure SgT4 (s p r : BitVec 64) (x : String) (H : List (Nat × Nat)) (q : BitVec 64)
    (rv R : Nat → BitVec 64) (M Mp : Mem) (img : Nat → BitVec 8) : Prop where
  h8 : R 8 = q
  h2 : R 2 = s + 18446744073709551504#64
  hk : ∀ y ∈ fRegs, y ∉ callerSaved → y ≠ 2 → y ≠ 8 → y ≠ 9 → R y = rv y
  sra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = rv 9
  hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k
  hcopy : CStrImg img q.toNat x
  hfresh : FreshBlock vsaLayoutP H q.toNat (x.toList.length + 1) ∧ q.toNat % 16 = 0

/-- A C string's bytes, moved from `b` to `q`. -/
theorem cstrImg_shift {img : Nat → BitVec 8} {b q : Nat} {x : String} (h : CStrImg img b x) :
    CStrImg (fun a => img (a - q + b)) q x :=
  ⟨fun i hi => by simp only [show q + i - q + b = b + i by omega]; exact h.1 i hi,
    by simp only [show q + x.toList.length - q + b = b + x.toList.length by omega]; exact h.2⟩

/-- **`memcpy(q, buf, len + 1)`** from `malloc`'s return. -/
theorem sg_memcpy (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (cx : SgCtx live p s r rv) (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) {q : BitVec 64}
    {R : Nat → BitVec 64} {M : Mem} (f : SgT3 s p r x H q rv R M Mp)
    (hB : ∀ R' M' img, SgT4 s p r x H q rv R' M' Mp img →
      SgRestC Wp Φ N inp p s r v x ρ H o rv Mp q img ∗ ms 0x80003070#64 R' (sgF s p) M' ⊢ Wp.W Φ) :
    SgRestB Wp Φ N inp p s r v x ρ H o rv Mp q ∗ ms 0x8000305c#64 R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hlen := f.hlen
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hq0 : q ≠ 0#64 := fun h => f.hfresh.1.nonzero (by rw [h]; rfl)
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := R) (Mt := M) (pc := 0x8000305c#64)
    (F := SgRestB Wp Φ N inp p s r v x ρ H o rv Mp q)
  rotate_left
  · unfold SgRestB
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine sg_copy cx.hlive f.h2 (by omega) hs2 hs3 cx.hg.al
    (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi (by rw [f.h10]; exact hq0) ?_
  intros; apply swp_closeF
  dsimp only [F']
  have eB : (s + 18446744073709551504#64 + 16#64).toNat = s.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have hsub : ∀ k, InExt (s.toNat - 96, x.toList.length + 1) k → sgF s p k := fun k hk =>
    .inl (by simp only [InExt] at hk ⊢; omega)
  have hsl : ∀ k, sgF s p k ↔ ((sgF s p k ∧ ¬ InExt (s.toNat - 96, x.toList.length + 1) k) ∨
      InExt (s.toNat - 96, x.toList.length + 1) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (s.toNat - 96, x.toList.length + 1) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hsub k h
  have hfr := f.hfresh.1
  have hq1 := hfr.lo; have hq2 := hfr.hi
  simp only [vsaLayoutP, Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd] at hq1 hq2
  iintro ⟨Hrest, Hms⟩
  ihave Hms := ms_iff hsl $$ Hms
  ihave ⟨Hms, HB⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  unfold SgRestB
  icases Hrest with ⟨#Hcode, #Himg, #Hv, Hh, Hblk, Hstd, Hcon, Hst, Hk⟩
  ihave #Hmc0 := hmc
  unfold memcpySpecOwned
  ihave #Hmcs := Hmc0 $$ %q %(s + 18446744073709551504#64 + 16#64) %(x.toList.length + 1) %(imgM M)
  unfold memcpyPC
  rw [eB]
  iapply (ms_callRegs Wp (i := 0x8000306c)
    (jalx_8000306c live (fun q hq => cx.hlive _ (interp_code_8000306c q hq))) interp_code_8000306c
    (L := [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31])
    (K := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27])
    (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin q.toNat (x.toList.length + 1) ∧
        htifLo + 16 ≤ q.toNat ∧ RamWin (s.toNat - 96) (x.toList.length + 1)⌝ ∗
      (10 : Nat) ↦ᵣ q ∗ (11 : Nat) ↦ᵣ (s + 18446744073709551504#64 + 16#64) ∗
      (12 : Nat) ↦ᵣ BitVec.ofNat 64 (x.toList.length + 1) ∗ clobbered argClob ∗
      blockOwn q.toNat (x.toList.length + 1) ∗
      ownImg (InExt (s.toNat - 96, x.toList.length + 1)) (imgM M) ∗ binImg))
    (Q := fun _ => iprop((10 : Nat) ↦ᵣ q ∗ clobbered retClob ∗
      ownImg (InExt (q.toNat, x.toList.length + 1)) (fun a => imgM M (a - q.toNat + (s.toNat - 96))) ∗
      ownImg (InExt (s.toNat - 96, x.toList.length + 1)) (imgM M)))
    (X := iprop(blockOwn q.toNat (x.toList.length + 1) ∗
      ownImg (InExt (s.toNat - 96, x.toList.length + 1)) (imgM M) ∗ binImg))
    (Y := fun g => iprop(⌜g 10 = q⌝ ∗
      ownImg (InExt (q.toNat, x.toList.length + 1)) (fun a => imgM M (a - q.toNat + (s.toNat - 96))) ∗
      ownImg (InExt (s.toNat - 96, x.toList.length + 1)) (imgM M)))
    (R := upd (upd (upd R 12 (ldv .ld M (s + 18446744073709551504#64 + 8#64).toNat)) 8 (R 10)) 11 (R 9))
    (S := fun a => sgF s p a ∧ ¬ InExt (s.toNat - 96, x.toList.length + 1) a) (Mt := M)
    ?hP ?hQ)
  case hP =>
    simp only [sepL_cons, sepL_nil]
    iintro ⟨⟨H10, H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩, Hbk, HB, #Hbi⟩
    iframe Hbk HB Hbi
    isplitl []
    · ipureintro
      refine ⟨by decide, ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩,
        by unfold htifLo; omega, ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩⟩
    isplitl [H10]
    · ix_reg; rw [f.h10]; iexact H10
    isplitl [H11]
    · ix_reg; rw [f.h9]; iexact H11
    isplitl [H12]
    · ix_reg; rw [f.sn]; iexact H12
    iapply clobbered_of_fn argClob _
    unfold argClob
    simp only [sepL_cons, sepL_nil]
    iframe H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31
  case hQ =>
    iintro ⟨H10, Hcl, Hd, HB⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn retClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then q else g y)
    unfold retClob argClob
    simp only [sepL_cons, sepL_nil]
    icases Hcl with ⟨H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩
    simp only [ite_true]
    simp (config := { decide := true }) only [ite_false]
    iframe H10 H11 H12 H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31 Hd HB
  iframe Hmcs Hcode Hms Hblk HB Himg
  iintro %g ⟨%hg10, Hd, HB⟩ Hms
  ihave ⟨%M2, Hms, %⟨hM2a, hM2b, -⟩⟩ := ms_join $$ [Hms HB]
  · iframe Hms HB
  ihave Hms := ms_iff (fun k => (hsl k).symm) $$ Hms
  have hM2 : ∀ k, sgF s p k → imgM M2 k = imgM M k := fun k hk => by
    by_cases h : InExt (s.toNat - 96, x.toList.length + 1) k
    · exact hM2b k h
    · exact hM2a k ⟨hk, h⟩
  have hoff : ∀ k, k < 112 → (s + 18446744073709551504#64 + BitVec.ofNat 64 k).toNat =
      s.toNat - 112 + k := by
    intro k hk; rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have hld : ∀ o, 16 ≤ o → o + 8 ≤ 112 →
      ldv .ld M2 (s + 18446744073709551504#64 + BitVec.ofNat 64 o).toNat =
      ldv .ld M (s + 18446744073709551504#64 + BitVec.ofNat 64 o).toNat := fun o h1 h2 => by
    rw [hoff o (by omega)]
    exact ldv_agree fun j hj => hM2 _ (.inl (by simp only [InExt]; omega))
  iapply (hB _ M2 _ ?t4)
  rotate_left
  · unfold SgRestC
    iframe Hcode Hv Hh Hd Hstd Hcon Hst Hk Hms
  case t4 =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, cstrImg_shift f.hbuf, f.hfresh⟩
    · ix_reg; exact f.h10
    · ix_reg; exact f.h2
    · intro y hy hc hy2 hy8 hy9
      have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
      have hK : y ∉ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] :=
        fun h => hc ((show ∀ z ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31],
          z ∈ callerSaved by decide) y h)
      have hy11 : y ≠ 11 := fun e => hK (by simp [e])
      have hy12 : y ≠ 12 := fun e => hK (by simp [e])
      simp only [upd, hy1, hy8, hy11, hy12, hK, ite_false]
      exact f.hk y hy hc hy2 hy9
    · rw [hld 104 (by omega) (by omega)]; exact f.sra
    · rw [hld 96 (by omega) (by omega)]; exact f.ss0
    · rw [hld 88 (by omega) (by omega)]; exact f.ss1
    · intro k hk
      rw [hM2 k (.inr hk)]; exact f.hslot k hk

/-- The return: `ra`, `a0 = s0 = q`, `s0`/`s1` restored, `sp = s`; the
continuation's post branch. -/
theorem sg_ret {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (cx : SgCtx live p s r rv) {q : BitVec 64} {R : Nat → BitVec 64} {M : Mem}
    {img : Nat → BitVec 8} (f : SgT4 s p r x H q rv R M Mp img) :
    SgRestC Wp Φ N inp p s r v x ρ H o rv Mp q img ∗
      ms r (upd (upd (upd (upd (upd R 1 r) 10 (R 8)) 8 (rv 8)) 9 (rv 9)) 2
        (s + 18446744073709551504#64 + 112#64)) (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  unfold SgRestC ms
  iintro ⟨⟨#Hcode, #Hv, Hh, Hd, Hstd, Hcon, Hst, Hk⟩, ⟨Hpc, Hra, Hregs, HS⟩⟩
  ihave ⟨HF, HP⟩ := ownSet_split_tracked _ _ M cx.hdsp $$ HS
  ihave HF := ownSet_forget _ _ $$ HF
  ihave Hst := sgFrame_join (s := s) (by unfold stringifyNeed snprintfNeed; omega) $$ [Hst HF]
  · iframe Hst HF
  rw [← valImg_agreeOn (GF := GF) (N := N) (v := v) (fun k hk => f.hslot k hk)]
  ihave Hval := valAt_of_img N $$ [Hv HP]
  · iframe Hv HP
  ihave Hra := ptsto_eq (show _ = r by ix_reg) $$ Hra
  ihave Hk := and_elim_l $$ Hk
  iapply Hk $$ Hpc Hra
  iexists _, q
  iframe Hregs Hval Hh Hstd Hcon
  isplitl []
  · ipureintro
    intro y hy hc
    have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
    have hy10 : y ≠ 10 := fun e => by subst e; exact hc (by decide)
    by_cases h2 : y = 2
    · subst h2; ix_reg
      rw [BitVec.add_assoc, show (18446744073709551504#64 : BitVec 64) + 112#64 = 0#64 by decide,
        BitVec.add_zero, cx.h2]
    by_cases h8 : y = 8
    · subst h8; ix_reg
    by_cases h9 : y = 9
    · subst h9; ix_reg
    simp only [upd, hy1, hy10, h2, h8, h9, ite_false]
    exact f.hk y hy hc h2 h8 h9
  isplitl []
  · ipureintro; ix_reg; exact f.h8
  isplitl [Hd]
  · unfold strOwn
    iexists img
    iframe Hd
    ipureintro; exact f.hcopy
  isplitl []
  · ipureintro; exact f.hfresh
  unfold stackAt
  iframe Hst
  ipureintro
  exact ⟨by unfold stringifyNeed snprintfNeed; omega,
    by unfold Vsa.Sim.LayoutInstance.stackSL stringifyNeed snprintfNeed; simp; omega,
    by unfold Vsa.Sim.LayoutInstance.stackSL; simp; omega, hs3, cx.hs4⟩

/-- **The epilogue and the return** after `memcpy`: the block holds the
rendering, the value's slot and the stack come back. -/
theorem sg_finish (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (cx : SgCtx live p s r rv) {q : BitVec 64} {R : Nat → BitVec 64} {M : Mem}
    {img : Nat → BitVec 8} (f : SgT4 s p r x H q rv R M Mp img) (pc : BitVec 64)
    (hpc : pc = 0x80003070#64 ∨ pc = 0x80003110#64) :
    SgRestC Wp Φ N inp p s r v x ρ H o rv Mp q img ∗ ms pc R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := R) (Mt := M) (pc := pc)
    (F := SgRestC Wp Φ N inp p s r v x ρ H o rv Mp q img)
  rotate_left
  · unfold SgRestC
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  rcases hpc with rfl | rfl
  · refine sg_epi cx.hlive f.h2 (by omega) hs2 hs3 cx.hg.al
      (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi cx.hal f.sra f.ss0
      f.ss1 ?_
    apply swp_closeF
    dsimp only [F']
    exact sg_ret cx f
  · refine sg_sepi cx.hlive f.h2 (by omega) hs2 hs3 cx.hg.al
      (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi cx.hal f.sra f.ss0
      f.ss1 ?_
    apply swp_closeF
    dsimp only [F']
    exact sg_ret cx f

/-- **`malloc(len + 1)`**, then the out-of-memory abort or the copy, the
epilogue and the return (the buffer arms' shared tail from `jal malloc`). -/
theorem sg_malloc (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hc : vsaChg (x.toList.length + 1) c)
    {R : Nat → BitVec 64} {M : Mem} (f : SgT2 s p r x rv R M Mp) :
    SgRest Wp Φ N inp p s r v x ρ H c o rv Mp ∗
      ms 0x80003058#64 R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hlen := f.hlen
  have e112 : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
    rw [BitVec.toNat_add]; simp; omega
  have hn : stringifyNeed - 112 ≤ (s + 18446744073709551504#64).toNat := by
    rw [e112]; unfold stringifyNeed snprintfNeed; omega
  have hm : allocHeadroom ≤ stringifyNeed - 112 := by unfold allocHeadroom stringifyNeed snprintfNeed; omega
  iintro ⟨Hrest, Hms⟩
  unfold SgRest
  icases Hrest with ⟨#Hcode, #Himg, #Hat, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hn hm $$ Hst
  rw [← f.h2]
  iapply (ms_callMalloc A Wp (i := 0x80003058)
    (jalx_80003058 live (fun q hq => cx.hlive _ (interp_code_80003058 q hq))) interp_code_80003058
    (by decide) ρ H c (R := R) (by rw [f.h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hc)
    ⟨by rw [f.h2, e112]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega,
      by rw [f.h2, e112]; omega, by rw [f.h2, e112]; omega⟩)
  iframe Hat Hcode Hms Hst Hh
  iintro %R' %hk' Hst Hres Hms
  rw [f.h2]
  ihave Hst := stackScratch_widen hn hm $$ [Hslack Hst]
  · iframe Hslack Hst
  rw [f.h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.toList.length + 1 < 2 ^ 64 by omega)]
  have k' : ∀ y ∈ fRegs, y ∉ callerSaved → R' y = R y := fun y hy hc => hk' y hy hc
  unfold mallocRes
  icases Hres with (⟨%⟨h0, hρ⟩, Hh⟩ | ⟨%hf, Hh, Hb⟩)
  · subst hρ
    iapply sg_oomPath Wp HN cx rfl (c := c) (pc := 0x8000305c) (.inl rfl)
      (R := upd R' 1 (BitVec.ofNat 64 (0x80003058 + 4))) (M := M)
      (by ix_reg; rw [k' 2 (by decide) (by decide)]; exact f.h2) (by ix_reg; exact h0)
    unfold SgRest
    rw [Regime.plus_uncounted]
    iframe Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms
  · iapply sg_memcpy Wp cx hmc (q := R' 10) (R := upd R' 1 (BitVec.ofNat 64 (0x80003058 + 4)))
      (M := M) (f := ⟨by ix_reg, by ix_reg; rw [k' 9 (by decide) (by decide)]; exact f.h9,
        by ix_reg; rw [k' 2 (by decide) (by decide)]; exact f.h2,
        fun y hy hc hy2 hy9 => by
          have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
          simp only [upd, hy1, ite_false]
          rw [k' y hy hc]; exact f.hk y hy hc hy2 hy9,
        f.sra, f.ss0, f.ss1, f.sn, f.hslot, f.hbuf, f.hlen, hf⟩)
      (fun R2 M2 img f4 => sg_finish Wp cx f4 _ (.inl rfl))
    unfold SgRestB
    iframe Hcode Himg Hv Hh Hb Hstd Hcon Hst Hk Hms

/-- **The buffer arms' shared tail**, from `jal strlen` to the return or the
out-of-memory abort. -/
theorem sg_tail (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hc : vsaChg (x.toList.length + 1) c)
    {R : Nat → BitVec 64} {M : Mem} (f : SgT1 s p r x rv R M Mp) :
    SgRest Wp Φ N inp p s r v x ρ H c o rv Mp ∗ ms 0x80003048#64 R (sgF s p) M ⊢ Wp.W Φ :=
  sg_strlen Wp cx f fun _ _ f2 => sg_malloc Wp A HN cx hmc hc f2

/-- The frame words the prologue saved, through later stores into the frame. -/
theorem sg_offs {s : BitVec 64} (hs : 112 ≤ s.toNat) :
    ∀ k, k < 112 → (s + 18446744073709551504#64 + BitVec.ofNat 64 k).toNat = s.toNat - 112 + k := by
  intro k hk; rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega

/-- **`null`**: `"null"` stored inline, then the shared tail. -/
theorem sg_nullArm (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {st : Store} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hc : vsaChg ("null".toList.length + 1) c)
    {M : Mem} (hk : ldv .lw M p.toNat = 0#64)
    (hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k) :
    SgRest Wp Φ N inp p s r .null "null" ρ H c o rv Mp ∗
      ms stringifyPC (upd rv 1 r) (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff := sg_offs (s := s) (by omega)
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := upd rv 1 r) (Mt := M) (pc := stringifyPC)
    (F := SgRest Wp Φ N inp p s r .null "null" ρ H c o rv Mp)
  rotate_left
  · unfold SgRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine sg_null cx.hlive cx.h10 cx.h2 (by omega) hs2 hs3 cx.hg.al
    (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi hk ?_
  intros; apply swp_closeF
  dsimp only [F']
  have e16 : (s + 18446744073709551504#64 + 16#64).toNat = s.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have e20 : (s + 18446744073709551504#64 + 16#64 + 4#64).toNat = s.toNat - 96 + 4 := by
    rw [BitVec.toNat_add, e16]; simp; omega
  refine sg_tail Wp A HN cx hmc hc ⟨by ix_reg, by ix_reg, by ix_reg, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  rotate_right
  · rw [e20, e16]; exact cstr_null _ _
  · intro y hy hc' hy2 hy9
    have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
    have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc' (e ▸ hz)
    have := hcl 10 (by decide); have := hcl 14 (by decide); have := hcl 15 (by decide)
    simp only [upd, hy1, hy2, hy9, *, ite_false]
  all_goals first
    | (rw [e20, e16]
       simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
       simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit])
    | (intro k hk'
       have hn := cx.hdsp k
       simp only [InExt] at hk' hn
       rw [e20, e16]
       simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
       simp (disch := omega) only [imgM_store_miss]
       exact hslot k (by simp only [InExt]; omega))

/-- **A native**: `"<native fn>"` from `.rodata`, stored inline, then the shared tail. -/
theorem sg_natArm (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {st : Store} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) {f : NativeFn} (hc : vsaChg ("<native fn>".toList.length + 1) c)
    {M : Mem} (hk : ldv .lw M p.toNat = 5#64)
    (hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k) :
    SgRest Wp Φ N inp p s r (.native f) "<native fn>" ρ H c o rv Mp ∗
      ms stringifyPC (upd rv 1 r) (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff := sg_offs (s := s) (by omega)
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := upd rv 1 r) (Mt := M) (pc := stringifyPC)
    (F := SgRest Wp Φ N inp p s r (.native f) "<native fn>" ρ H c o rv Mp)
  rotate_left
  · unfold SgRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine sg_nat cx.hlive cx.h10 cx.h2 (by omega) hs2 hs3 cx.hg.al
    (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi hk ?_
  intros; apply swp_closeF
  dsimp only [F']
  have e16 : (s + 18446744073709551504#64 + 16#64).toNat = s.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have e20 : (s + 18446744073709551504#64 + 16#64 + 8#64).toNat = s.toNat - 96 + 8 := by
    rw [BitVec.toNat_add, e16]; simp; omega
  refine sg_tail Wp A HN cx hmc hc ⟨by ix_reg, by ix_reg, by ix_reg, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  rotate_right
  · rw [e20, e16]; exact cstr_native _ _
  · intro y hy hc' hy2 hy9
    have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
    have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc' (e ▸ hz)
    have := hcl 10 (by decide); have := hcl 14 (by decide); have := hcl 15 (by decide)
    simp only [upd, hy1, hy2, hy9, *, ite_false]
  all_goals first
    | (rw [e20, e16]
       simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
       simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit])
    | (intro k hk'
       have hn := cx.hdsp k
       simp only [InExt] at hk' hn
       rw [e20, e16]
       simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
       simp (disch := omega) only [imgM_store_miss]
       exact hslot k (by simp only [InExt]; omega))

/-- At a call's return into the buffer arms (`strcpy`, `snprintf`): the
buffer is out of the run's bytes. -/
structure SgTB (s p r : BitVec 64) (rv R : Nat → BitVec 64) (M Mp : Mem) : Prop where
  h9 : R 9 = s + 18446744073709551504#64 + 16#64
  h2 : R 2 = s + 18446744073709551504#64
  hk : ∀ y ∈ fRegs, y ∉ callerSaved → y ≠ 2 → y ≠ 9 → R y = rv y
  sra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = rv 9
  hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k

/-- The run's bytes without the buffer `[sp + 16, sp + 80)`. -/
abbrev sgFnb (s p : BitVec 64) (k : Nat) : Prop :=
  sgF s p k ∧ ¬ InExt (s.toNat - 96, 64) k

/-- **The buffer filled by a call**: back in, the run to `jal strlen`, the
shared tail. -/
theorem sg_filled (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hc : vsaChg (x.toList.length + 1) c)
    (hlen : x.toList.length ≤ 63) {pc : BitVec 64}
    (hpc : pc = 0x80003010#64 ∨ pc = 0x800030dc#64 ∨ pc = 0x80003044#64)
    {R : Nat → BitVec 64} {M : Mem} (f : SgTB s p r rv R M Mp) :
    SgRest Wp Φ N inp p s r v x ρ H c o rv Mp ∗ ms pc R (sgFnb s p) M ∗
      (∃ img, ownImg (InExt (s.toNat - 96, 64)) img ∗ ⌜CStrImg img (s.toNat - 96) x⌝) ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hsl : ∀ k, (sgFnb s p k ∨ InExt (s.toNat - 96, 64) k) ↔ sgF s p k := fun k => by
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact .inl (by simp only [InExt] at h ⊢; omega)
    · intro h; by_cases h' : InExt (s.toNat - 96, 64) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
  iintro ⟨Hrest, Hms, ⟨%img, HB, %hx⟩⟩
  ihave ⟨%Mi, HB, %hMi⟩ := ownSet_trackedAt _ img $$ HB
  ihave ⟨%M1, Hms, %⟨h1a, h1b, -⟩⟩ := ms_join $$ [Hms HB]
  · iframe Hms HB
  ihave Hms := ms_iff hsl $$ Hms
  have hoff := sg_offs (s := s) (by omega)
  have hld : ∀ o, 16 ≤ o → o + 8 ≤ 112 → (o + 8 ≤ 16 ∨ 80 ≤ o) →
      ldv .ld M1 (s + 18446744073709551504#64 + BitVec.ofNat 64 o).toNat =
      ldv .ld M (s + 18446744073709551504#64 + BitVec.ofNat 64 o).toNat := fun o h1 h2 h3 => by
    rw [hoff o (by omega)]
    exact ldv_agree fun j hj => h1a _ ⟨.inl (by simp only [InExt]; omega),
      by simp only [InExt]; omega⟩
  iapply wp_swpF Wp (S := sgF s p) (R := R) (Mt := M1) (pc := pc)
    (F := SgRest Wp Φ N inp p s r v x ρ H c o rv Mp)
  rotate_left
  · unfold SgRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  have gl : (0x87800000 + 112 ≤ s.toNat) ∧ p.toNat % 8 = 0 ∧ 0x8001ad00 + 16 ≤ p.toNat ∧
      p.toNat + 24 ≤ 0x100000000 :=
    ⟨by omega, cx.hg.al, by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega, cx.hg.hi⟩
  have kont : ∀ R' : Nat → BitVec 64, R' 10 = R 9 → (∀ y, y ≠ 10 → y ≠ 1 → R' y = R y) →
      SWP live (interpText ++ dataOf ∅ []) iRegs (sgF s p)
        (RunK Wp Φ F' (sgF s p)) 0x80003048#64 R' M1 := fun R' h10 h' => by
    apply swp_closeF
    dsimp only [F']
    refine sg_tail Wp A HN cx hmc hc ⟨by rw [h10, f.h9], by rw [h' 9 (by decide) (by decide), f.h9],
      by rw [h' 2 (by decide) (by decide), f.h2], fun y hy hc' hy2 hy9 => ?_,
      by rw [hld 104 (by omega) (by omega) (by omega)]; exact f.sra,
      by rw [hld 96 (by omega) (by omega) (by omega)]; exact f.ss0,
      by rw [hld 88 (by omega) (by omega) (by omega)]; exact f.ss1,
      fun k hk => ?_, ?_, hlen⟩
    · have hy10 : y ≠ 10 := fun e => hc' (by rw [e]; decide)
      have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
      rw [h' y hy10 hy1]; exact f.hk y hy hc' hy2 hy9
    · have hn := cx.hdsp k
      rw [h1a k ⟨.inr hk, fun h => hn (by simp only [InExt] at h ⊢; omega) hk⟩]
      exact f.hslot k hk
    · exact cstrImg_congr hx fun i hi => by
        rw [h1b _ (by simp only [InExt]; omega)]; exact hMi _ (by simp only [InExt]; omega)
  rcases hpc with rfl | rfl | rfl
  · exact sg_back cx.hlive f.h2 gl.1 hs2 hs3 gl.2.1 gl.2.2.1 gl.2.2.2 fun _ =>
      kont _ (by ix_reg) (fun y h10 h1 => by simp [upd, h10, h1])
  · exact sg_backInt cx.hlive f.h2 gl.1 hs2 hs3 gl.2.1 gl.2.2.1 gl.2.2.2 fun _ =>
      kont _ (by ix_reg) (fun y h10 h1 => by simp [upd, h10, h1])
  · exact sg_backFn cx.hlive f.h2 gl.1 hs2 hs3 gl.2.1 gl.2.2.1 gl.2.2.2 fun _ =>
      kont _ (by ix_reg) (fun y h10 h1 => by simp [upd, h10, h1])

/-- **`strcpy(buf, src)`** of a read-only C string (the bool arm), then the
buffer-filled continuation. -/
theorem sg_strcpy (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hsc : binImg (GF := GF) ⊢ strcpySpec (vsaModel live) Wp)
    (hc : vsaChg (x.toList.length + 1) c) (hlen : x.toList.length ≤ 63) {src : BitVec 64}
    (hsrc : binImg (GF := GF) ⊢ strAt src.toNat x)
    {R : Nat → BitVec 64} {M : Mem} (h10 : R 10 = s + 18446744073709551504#64 + 16#64)
    (h11 : R 11 = src) (f : SgTB s p r rv R M Mp) :
    SgRest Wp Φ N inp p s r v x ρ H c o rv Mp ∗ ms 0x8000300c#64 R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have eB : (s + 18446744073709551504#64 + 16#64).toNat = s.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have hsl : ∀ k, sgF s p k ↔ (sgFnb s p k ∨ InExt (s.toNat - 96, 64) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (s.toNat - 96, 64) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact .inl (by simp only [InExt] at h ⊢; omega)
  iintro ⟨Hrest, Hms⟩
  ihave Hms := ms_iff hsl $$ Hms
  ihave ⟨Hms, HB⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  ihave HB := ownSet_forget _ _ $$ HB
  unfold SgRest
  icases Hrest with ⟨#Hcode, #Himg, #Hat, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
  ihave #Hs := hsrc $$ Himg
  ihave #Hsc0 := hsc $$ Himg
  unfold strcpySpec
  ihave #Hscs := Hsc0 $$ %(s + 18446744073709551504#64 + 16#64) %src %x %64
  rw [eB]
  iapply (ms_callRegs Wp (i := 0x8000300c)
    (jalx_8000300c live (fun q hq => cx.hlive _ (interp_code_8000300c q hq))) interp_code_8000300c
    (L := [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31])
    (K := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27])
    (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin (s.toNat - 96) 64 ∧ x.toList.length + 1 ≤ 64 ∧
        htifLo + 16 ≤ s.toNat - 96⌝ ∗
      (10 : Nat) ↦ᵣ (s + 18446744073709551504#64 + 16#64) ∗ (11 : Nat) ↦ᵣ src ∗
      clobbered (12 :: argClob) ∗ blockOwn (s.toNat - 96) 64 ∗ strAt src.toNat x))
    (Q := fun _ => iprop((10 : Nat) ↦ᵣ (s + 18446744073709551504#64 + 16#64) ∗ clobbered retClob ∗
      (∃ img, ownImg (InExt (s.toNat - 96, 64)) img ∗ ⌜CStrImg img (s.toNat - 96) x⌝)))
    (X := iprop(blockOwn (s.toNat - 96) 64 ∗ strAt src.toNat x))
    (Y := fun g => iprop(⌜g 10 = s + 18446744073709551504#64 + 16#64⌝ ∗
      (∃ img, ownImg (InExt (s.toNat - 96, 64)) img ∗ ⌜CStrImg img (s.toNat - 96) x⌝)))
    (R := R) (S := sgFnb s p) (Mt := M) ?hP ?hQ)
  case hP =>
    simp only [sepL_cons, sepL_nil]
    iintro ⟨⟨H10, H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩, Hbk, #Hs'⟩
    iframe Hbk Hs'
    isplitl []
    · ipureintro
      refine ⟨by decide, ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩, by omega,
        by unfold htifLo; omega⟩
    isplitl [H10]
    · rw [h10]; iexact H10
    isplitl [H11]
    · rw [h11]; iexact H11
    iapply clobbered_of_fn (12 :: argClob) R
    unfold argClob
    simp only [sepL_cons, sepL_nil]
    iframe H12 H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31
  case hQ =>
    iintro ⟨H10, Hcl, Hd⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn retClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then s + 18446744073709551504#64 + 16#64 else g y)
    unfold retClob argClob
    simp only [sepL_cons, sepL_nil]
    icases Hcl with ⟨H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩
    simp only [ite_true]
    simp (config := { decide := true }) only [ite_false]
    iframe H10 H11 H12 H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31 Hd
  unfold blockOwn
  iframe Hscs Hcode Hms HB Hs
  iintro %g ⟨%hg10, Hd⟩ Hms
  iapply sg_filled Wp A HN cx hmc hc hlen (pc := 0x80003010#64) (.inl rfl)
    (R := upd (fun y => if y ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] then g y
      else R y) 1 (BitVec.ofNat 64 (0x8000300c + 4))) (M := M)
    ⟨by ix_reg; exact f.h9, by ix_reg; exact f.h2, fun y hy hc' hy2 hy9 => by
        have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
        have hK : y ∉ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] :=
          fun h => hc' ((show ∀ z ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31],
            z ∈ callerSaved by decide) y h)
        simp only [upd, hy1, hK, ite_false]
        exact f.hk y hy hc' hy2 hy9,
      f.sra, f.ss0, f.ss1, f.hslot⟩
  unfold SgRest
  iframe Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms Hd


/-- **A bool**: `strcpy(buf, b ? "true" : "false")`, then the shared tail. -/
theorem sg_boolArm (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hsc : binImg (GF := GF) ⊢ strcpySpec (vsaModel live) Wp)
    {b : Bool} (hc : vsaChg ((if b then "true" else "false").toList.length + 1) c) {M : Mem}
    (hk : ldv .lw M p.toNat = 1#64) (hb : ldv .lw M (p + 8#64).toNat = if b then 1#64 else 0#64)
    (hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k) :
    SgRest Wp Φ N inp p s r (.bool b) (if b then "true" else "false") ρ H c o rv Mp ∗
      ms stringifyPC (upd rv 1 r) (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff := sg_offs (s := s) (by omega)
  have hsep := cx.sep
  have hp1 := cx.hg.al; have hp2 := cx.hg.lo; have hp3 := cx.hg.hi
  unfold Vsa.Sim.tohostAddr at hp2
  have ep8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hb' : ldv .lw (writeLog (writeLog (writeLog M
      [((s + 18446744073709551504#64 + 104#64).toNat, 8, r)])
      [((s + 18446744073709551504#64 + 96#64).toNat, 8, rv 8)])
      [((s + 18446744073709551504#64 + 88#64).toNat, 8, rv 9)]) (p.toNat + 8) =
      if b then 1#64 else 0#64 := by
    rw [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
    simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss]
    rw [← ep8]; exact hb
  have fB : ∀ (R' : Nat → BitVec 64), R' 9 = s + 18446744073709551504#64 + 16#64 →
      R' 2 = s + 18446744073709551504#64 →
      (∀ y, y ≠ 1 → y ≠ 2 → y ≠ 9 → y ≠ 10 → y ≠ 11 → y ≠ 14 → y ≠ 15 → R' y = rv y) →
      SgTB s p r rv R' (writeLog (writeLog (writeLog M
        [((s + 18446744073709551504#64 + 104#64).toNat, 8, r)])
        [((s + 18446744073709551504#64 + 96#64).toNat, 8, rv 8)])
        [((s + 18446744073709551504#64 + 88#64).toNat, 8, rv 9)]) Mp := fun R' h9 h2 hk' => by
    refine ⟨h9, h2, fun y hy hc' hy2 hy9 => ?_, ?_, ?_, ?_, fun k hk => ?_⟩
    · have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc' (e ▸ hz)
      exact hk' y (fun e => by subst e; revert hy; decide) hy2 hy9 (hcl 10 (by decide))
        (hcl 11 (by decide)) (hcl 14 (by decide)) (hcl 15 (by decide))
    all_goals first
      | (simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
         simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit])
      | (simp only [InExt] at hk
         simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
         simp (disch := omega) only [imgM_store_miss]
         exact hslot k (by simp only [InExt]; omega))
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := upd rv 1 r) (Mt := M) (pc := stringifyPC)
    (F := SgRest Wp Φ N inp p s r (.bool b) (if b then "true" else "false") ρ H c o rv Mp)
  rotate_left
  · unfold SgRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine sg_bool cx.hlive cx.h10 cx.h2 (by omega) hs2 hs3 hp1 (by omega) hp3 hk hb ?_ ?_
  · intro _ _ _ _ _ _ hz
    cases b
    · apply swp_closeF
      dsimp only [F']
      exact sg_strcpy Wp A HN cx hmc hsc (x := "false") hc (by decide) (src := 0x80019010#64)
        (strAt_rodata (by rw [str_false]; decide) (by unfold CStrImg; rw [str_false]; decide)
          (by rw [str_false]; exact ⟨by decide, by decide, .inl (by unfold htifLo; decide)⟩))
        (by ix_reg) (by ix_reg) (fB _ (by ix_reg) (by ix_reg) (fun y h1 h2 h9 h10 h11 h14 h15 => by
          simp [upd, h1, h2, h9, h10, h11, h14, h15]))
    · exfalso; rw [hb'] at hz; exact absurd hz (by decide)
  · intro _ _ _ _ _ _ hz
    cases b
    · exfalso; rw [hb'] at hz; exact hz rfl
    · apply swp_closeF
      dsimp only [F']
      exact sg_strcpy Wp A HN cx hmc hsc (x := "true") hc (by decide) (src := 0x80019008#64)
        (strAt_rodata (by rw [str_true]; decide) (by unfold CStrImg; rw [str_true]; decide)
          (by rw [str_true]; exact ⟨by decide, by decide, .inl (by unfold htifLo; decide)⟩))
        (by ix_reg) (by ix_reg) (fB _ (by ix_reg) (by ix_reg) (fun y h1 h2 h9 h10 h11 h14 h15 => by
          simp [upd, h1, h2, h9, h10, h11, h14, h15]))

/-- **An integer**: `snprintf(buf, 64, "%lld", i)` (`Sym.snprintfInt_out`),
then the shared tail. -/
theorem sg_intArm (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (Hout : OutHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) {iw : BitVec 64}
    (hc : vsaChg ((intToString iw.toInt).toList.length + 1) c) {M : Mem}
    (hk : ldv .lw M p.toNat = 2#64) (hi : ldv .ld M (p + 8#64).toNat = iw)
    (hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k) :
    SgRest Wp Φ N inp p s r (.int iw.toInt) (intToString iw.toInt) ρ H c o rv Mp ∗
      ms stringifyPC (upd rv 1 r) (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff := sg_offs (s := s) (by omega)
  have hsep := cx.sep
  have hp1 := cx.hg.al; have hp2 := cx.hg.lo; have hp3 := cx.hg.hi
  unfold Vsa.Sim.tohostAddr at hp2
  have ep8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hi' : ldv .ld (writeLog (writeLog (writeLog M
      [((s + 18446744073709551504#64 + 104#64).toNat, 8, r)])
      [((s + 18446744073709551504#64 + 96#64).toNat, 8, rv 8)])
      [((s + 18446744073709551504#64 + 88#64).toNat, 8, rv 9)]) (p.toNat + 8) = iw := by
    rw [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
    simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss]
    rw [← ep8]; exact hi
  have eB : (s + 18446744073709551504#64 + 16#64).toNat = s.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have e112 : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
    rw [BitVec.toNat_add]; simp; omega
  have hsl : ∀ k, sgF s p k ↔ (sgFnb s p k ∨ InExt (s.toNat - 96, 64) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (s.toNat - 96, 64) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact .inl (by simp only [InExt] at h ⊢; omega)
  have hlen : (intToString iw.toInt).toList.length ≤ 63 := by
    have := intToString_len_le iw.toInt (by have := BitVec.le_toInt (x := iw); simp at this ⊢; omega)
      (by have := BitVec.toInt_lt (x := iw); simp at this ⊢; omega)
    omega
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := upd rv 1 r) (Mt := M) (pc := stringifyPC)
    (F := SgRest Wp Φ N inp p s r (.int iw.toInt) (intToString iw.toInt) ρ H c o rv Mp)
  rotate_left
  · unfold SgRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine sg_int cx.hlive cx.h10 cx.h2 (by omega) hs2 hs3 hp1 (by omega) hp3 hk hi ?_
  intros; apply swp_closeF
  dsimp only [F']
  rw [hi']
  iintro ⟨Hrest, Hms⟩
  ihave Hms := ms_iff hsl $$ Hms
  ihave ⟨Hms, HB⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  ihave HB := ownSet_forget _ _ $$ HB
  unfold SgRest
  icases Hrest with ⟨#Hcode, #Himg, #Hat, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
  ihave #Hgp := codeRes_gp $$ Hcode
  have hsg' : SpIn (s + 18446744073709551504#64) snprintfNeed :=
    ⟨by rw [e112]; unfold snprintfNeed Vsa.Sim.tohostAddr; omega, by rw [e112]; omega,
      by rw [e112]; omega⟩
  ihave #Hsp := snprintfInt_out live Wp (s + 18446744073709551504#64)
    (s + 18446744073709551504#64 + 16#64) iw
    (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd rv 1 r) 15 2#64) 2
      (s + 18446744073709551504#64)) 14 3#64) 14 2#64) 13 iw) 9 (s + 18446744073709551504#64 + 16#64))
      10 (s + 18446744073709551504#64 + 16#64)) 12 2147586252#64) 12 2147586752#64) 11 64#64)
    cx.hcl hsg' (by rw [e112]; unfold snprintfNeed; omega) (by rw [eB]; omega) (by rw [eB]; omega)
  unfold snprintfIntSpec
  rw [eB]
  iapply (ms_callNewlibA Wp (i := 0x800030d8)
    (jalx_800030d8 live (fun q hq => cx.hlive _ (interp_code_800030d8 q hq))) interp_code_800030d8
    (vs := [s + 18446744073709551504#64 + 16#64, 64#64, 0x800192c0#64, iw])
    (P := fun ra0 => iprop(⌜ra0.toNat % 4 = 0⌝ ∗ argsAt [s + 18446744073709551504#64 + 16#64, 64#64, 0x800192c0#64, iw] ∗
      blockOwn (s.toNat - 96) 64 ∗ stdioOwn ∗
      callFrame (s + 18446744073709551504#64) snprintfNeed Newlib.calleeSaved
        (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd rv 1 r) 15 2#64) 2
      (s + 18446744073709551504#64)) 14 3#64) 14 2#64) 13 iw) 9 (s + 18446744073709551504#64 + 16#64))
      10 (s + 18446744073709551504#64 + 16#64)) 12 2147586252#64) 12 2147586752#64) 11 64#64)))
    (Q := fun _ => iprop(clobbered argRegs ∗
      (∃ img, ownImg (InExt (s.toNat - 96, 64)) img ∗
        ⌜CStrImg img (s.toNat - 96) (intToString iw.toInt)⌝) ∗ stdioOwn ∗
      callFrame (s + 18446744073709551504#64) snprintfNeed Newlib.calleeSaved
        (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd rv 1 r) 15 2#64) 2
      (s + 18446744073709551504#64)) 14 3#64) 14 2#64) 13 iw) 9 (s + 18446744073709551504#64 + 16#64))
      10 (s + 18446744073709551504#64 + 16#64)) 12 2147586252#64) 12 2147586752#64) 11 64#64)))
    (X := iprop(blockOwn (s.toNat - 96) 64 ∗ stdioOwn))
    (Y := iprop((∃ img, ownImg (InExt (s.toNat - 96, 64)) img ∗
      ⌜CStrImg img (s.toNat - 96) (intToString iw.toInt)⌝) ∗ stdioOwn))
    (need := snprintfNeed) (n := stringifyNeed - 112) (s := s + 18446744073709551504#64)
    (R := upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd rv 1 r) 15 2#64) 2
      (s + 18446744073709551504#64)) 14 3#64) 14 2#64) 13 iw) 9 (s + 18446744073709551504#64 + 16#64))
      10 (s + 18446744073709551504#64 + 16#64)) 12 2147586252#64) 12 2147586752#64) 11 64#64)
    (S := sgFnb s p)
    (by simp) (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | _ | _ | j
      · simp [upd]
      · simp [upd]
      · simp [upd]
      · simp [upd]
      · omega)
    (by simp [upd]) (by rw [e112]; unfold stringifyNeed snprintfNeed; omega)
    (by unfold stringifyNeed; omega) (by decide)
    (fun _ hr => by
      iintro ⟨Ha, ⟨Hb, Hs⟩, Hf⟩
      isplitr
      · ipureintro; exact hr
      iframe Ha Hb Hs Hf)
    (fun _ => by iintro ⟨Ha, Hd, Hs, Hf⟩; iframe Ha Hd Hs Hf))
  unfold blockOwn snprintfEntry
  iframe Hsp Hcode Hms HB Hstd Hst Hgp Himg
  iintro %R' %hk' ⟨Hd, Hstd⟩ Hms Hst
  have k' : ∀ y ∈ fRegs, y ∉ callerSaved → R' y = _ := fun y hy hc' => hk' y hy hc'
  iapply sg_filled Wp A HN cx hmc hc hlen (pc := 0x800030dc#64) (.inr (.inl rfl))
    (R := upd R' 1 (BitVec.ofNat 64 (0x800030d8 + 4)))
    (M := writeLog (writeLog (writeLog M
      [((s + 18446744073709551504#64 + 104#64).toNat, 8, r)])
      [((s + 18446744073709551504#64 + 96#64).toNat, 8, rv 8)])
      [((s + 18446744073709551504#64 + 88#64).toNat, 8, rv 9)])
    ⟨by ix_reg; rw [k' 9 (by decide) (by decide)]; ix_reg,
      by ix_reg; rw [k' 2 (by decide) (by decide)]; ix_reg,
      fun y hy hc' hy2 hy9 => by
        have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
        have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc' (e ▸ hz)
        simp only [upd, hy1, ite_false]
        rw [k' y hy hc']
        simp only [upd, hy1, hy2, hy9, hcl 10 (by decide), hcl 11 (by decide), hcl 12 (by decide),
          hcl 13 (by decide), hcl 14 (by decide), hcl 15 (by decide), ite_false],
      by simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
         simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit],
      by simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
         simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit],
      by simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
         simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit],
      fun k hk => by
        simp only [InExt] at hk
        simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
        simp (disch := omega) only [imgM_store_miss]
        exact hslot k (by simp only [InExt]; omega)⟩
  unfold SgRest
  iframe Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms Hd

omit G in
/-- A C string's read window. -/
theorem strAt_win [MachGS hlc GF] {q : Nat} {t : String} :
    strAt (GF := GF) q t ⊢ ⌜StrWin q t.toList.length⌝ := by
  unfold strAt
  iintro ⟨%img, %⟨-, hw⟩, -⟩
  ipureintro; exact hw

omit G in
/-- A string value's meaning gives its payload's C string. -/
theorem valImg_str_strAt [MachGS hlc GF] {N : NativeAddrs} {img : Nat → BitVec 8} {a : Nat}
    {t : String} : valImg (GF := GF) N img a (.str t) ⊢ strAt (imgW img (a + 8)).toNat t := by
  simp only [valOf]
  iintro ⟨-, #H⟩
  iexact H

/-- The string arm at `jal malloc` (`0x800030f8`): `len + 1` in `a0` and `s1`,
the string's pointer at `sp + 8`. -/
structure SgS2 (s p r sw : BitVec 64) (x : String) (rv R : Nat → BitVec 64) (M Mp : Mem) : Prop where
  h10 : R 10 = BitVec.ofNat 64 (x.toList.length + 1)
  h9 : R 9 = BitVec.ofNat 64 (x.toList.length + 1)
  h2 : R 2 = s + 18446744073709551504#64
  hk : ∀ y ∈ fRegs, y ∉ callerSaved → y ≠ 2 → y ≠ 9 → R y = rv y
  sra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = rv 9
  sn : ldv .ld M (s + 18446744073709551504#64 + 8#64).toNat = sw
  hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k

/-- **A string**: its payload's `strlen` (H1's `strlenSpec`), the run to
`jal malloc`. -/
theorem sg_strHead (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (cx : SgCtx live p s r rv) (hsl : binImg (GF := GF) ⊢ strlenSpec Wp) {t : String} {M : Mem}
    (hk : ldv .lw M p.toNat = 3#64) (hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k)
    (hB : ∀ R' M', SgS2 s p r (imgW (imgM Mp) (p.toNat + 8)) t rv R' M' Mp →
      SgRest Wp Φ N inp p s r (.str t) t ρ H c o rv Mp ∗ ms 0x800030f8#64 R' (sgF s p) M' ⊢ Wp.W Φ) :
    SgRest Wp Φ N inp p s r (.str t) t ρ H c o rv Mp ∗
      ms stringifyPC (upd rv 1 r) (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff := sg_offs (s := s) (by omega)
  have hsep := cx.sep
  have hp1 := cx.hg.al; have hp2 := cx.hg.lo; have hp3 := cx.hg.hi
  unfold Vsa.Sim.tohostAddr at hp2
  have ep8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hsw0 : ldv .ld M (p.toNat + 8) = imgW (imgM Mp) (p.toNat + 8) := by
    rw [ldv_ld_imgW]
    exact imgW_agree fun j hj => hslot _ (by simp only [InExt]; omega)
  have hsw : ldv .ld M (p + 8#64).toNat = imgW (imgM Mp) (p.toNat + 8) := by
    rw [ep8]; exact hsw0
  have hsw' : ldv .ld (writeLog (writeLog (writeLog M
      [((s + 18446744073709551504#64 + 104#64).toNat, 8, r)])
      [((s + 18446744073709551504#64 + 96#64).toNat, 8, rv 8)])
      [((s + 18446744073709551504#64 + 88#64).toNat, 8, rv 9)]) (p.toNat + 8) =
      imgW (imgM Mp) (p.toNat + 8) := by
    rw [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
    simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss]
    exact hsw0
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := upd rv 1 r) (Mt := M) (pc := stringifyPC)
    (F := SgRest Wp Φ N inp p s r (.str t) t ρ H c o rv Mp)
  rotate_left
  · unfold SgRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine sg_str cx.hlive cx.h10 cx.h2 (by omega) hs2 hs3 hp1 (by omega) hp3 hk hsw ?_
  intros; apply swp_closeF
  dsimp only [F']
  rw [hsw']
  iintro ⟨Hrest, Hms⟩
  unfold SgRest
  icases Hrest with ⟨#Hcode, #Himg, #Hat, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
  ihave #Hs := valImg_str_strAt $$ Hv
  ihave %hwin := strAt_win $$ Hs
  ihave #Hsl0 := hsl $$ Himg
  unfold strlenSpec
  ihave #Hsls := Hsl0 $$ %(imgW (imgM Mp) (p.toNat + 8)) %t
  unfold strlenPC
  iapply (ms_callRegs Wp (i := 0x800030ec)
    (jalx_800030ec live (fun q hq => cx.hlive _ (interp_code_800030ec q hq))) interp_code_800030ec
    (L := [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31])
    (K := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27])
    (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ imgW (imgM Mp) (p.toNat + 8) ∗
      clobbered retClob ∗ strAt (imgW (imgM Mp) (p.toNat + 8)).toNat t))
    (Q := fun _ => iprop((10 : Nat) ↦ᵣ BitVec.ofNat 64 t.length ∗ clobbered retClob))
    (X := strAt (imgW (imgM Mp) (p.toNat + 8)).toNat t)
    (Y := fun g => iprop(⌜g 10 = BitVec.ofNat 64 t.length⌝))
    (R := upd (upd (upd (upd (upd (upd rv 1 r) 15 3#64) 2 (s + 18446744073709551504#64)) 14 3#64) 11
      (imgW (imgM Mp) (p.toNat + 8))) 10 (imgW (imgM Mp) (p.toNat + 8))) (S := sgF s p)
    (Mt := writeLog (writeLog (writeLog (writeLog M
      [((s + 18446744073709551504#64 + 104#64).toNat, 8, r)])
      [((s + 18446744073709551504#64 + 96#64).toNat, 8, rv 8)])
      [((s + 18446744073709551504#64 + 88#64).toNat, 8, rv 9)])
      [((s + 18446744073709551504#64 + 8#64).toNat, 8, imgW (imgM Mp) (p.toNat + 8))]) ?hP ?hQ)
  case hP =>
    simp only [sepL_cons, sepL_nil]
    iintro ⟨⟨H10, H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩, #Hs'⟩
    iframe Hs'
    isplitl []
    · ipureintro; decide
    isplitl [H10]
    · simp only [upd, ite_true]; iexact H10
    iapply clobbered_of_fn retClob _
    unfold retClob argClob
    simp only [sepL_cons, sepL_nil]
    iframe H11 H12 H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31
  case hQ =>
    iintro ⟨H10, Hcl⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn retClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then BitVec.ofNat 64 t.length else g y)
    unfold retClob argClob
    simp only [sepL_cons, sepL_nil]
    icases Hcl with ⟨H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩
    simp only [ite_true]
    simp (config := { decide := true }) only [ite_false]
    iframe H10 H11 H12 H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31
  iframe Hsls Hcode Hms Hs
  iintro %g %hg10 Hms
  iapply wp_swpF Wp (S := sgF s p) (pc := 0x800030f0#64)
    (F := SgRest Wp Φ N inp p s r (.str t) t ρ H c o rv Mp)
  rotate_left
  · rw [hro]; unfold SgRest
    iframe Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms
  intro F'
  refine sg_slen cx.hlive (by simp [upd]) (by omega) hs2 hs3 hp1 (by omega) hp3 ?_
  intros; apply swp_closeF
  dsimp only [F']
  have hlt : t.toList.length + 1 < 2 ^ 64 := by have := hwin.hi; omega
  have h1 : g 10 + 1#64 = BitVec.ofNat 64 (t.toList.length + 1) := by
    rw [hg10, ← String.length_toList]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show t.toList.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (show t.toList.length + 1 < 2 ^ 64 by omega)]
  refine hB _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ix_reg; exact h1
  · ix_reg; exact h1
  · simp [upd]
  · intro y hy hc' hy2 hy9
    have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
    have hK : y ∉ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] := fun h => hc' ((show ∀ z ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31],
      z ∈ callerSaved by decide) y h)
    have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc' (e ▸ hz)
    simp only [upd, hy1, hy9, hcl 10 (by decide), hK, ite_false]
    simp only [hy2, hcl 11 (by decide), hcl 14 (by decide), hcl 15 (by decide), ite_false]
  all_goals first
    | (simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega), hoff 8 (by omega)]
       simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit])
    | (intro k hk
       simp only [InExt] at hk
       simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega), hoff 8 (by omega)]
       simp (disch := omega) only [imgM_store_miss]
       exact hslot k (by simp only [InExt]; omega))

/-- The string arm at `malloc`'s return (`0x800030fc`) with the block `q`. -/
structure SgS3 (s p r sw : BitVec 64) (x : String) (H : List (Nat × Nat)) (q : BitVec 64)
    (rv R : Nat → BitVec 64) (M Mp : Mem) : Prop where
  h10 : R 10 = q
  h9 : R 9 = BitVec.ofNat 64 (x.toList.length + 1)
  h2 : R 2 = s + 18446744073709551504#64
  hk : ∀ y ∈ fRegs, y ∉ callerSaved → y ≠ 2 → y ≠ 9 → R y = rv y
  sra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = rv 9
  sn : ldv .ld M (s + 18446744073709551504#64 + 8#64).toNat = sw
  hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k
  hfresh : FreshBlock vsaLayoutP H q.toNat (x.toList.length + 1) ∧ q.toNat % 16 = 0

/-- **`memcpy(q, s, len + 1)`** from the string's read-only bytes (H1's
`memcpySpec`), then the epilogue and the return. -/
theorem sg_strCopy (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {ρ : Regime}
    {H : List (Nat × Nat)} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (cx : SgCtx live p s r rv) (hmcr : binImg (GF := GF) ⊢ memcpySpec Wp) {t : String} {q : BitVec 64}
    {R : Nat → BitVec 64} {M : Mem} (f : SgS3 s p r (imgW (imgM Mp) (p.toNat + 8)) t H q rv R M Mp) :
    SgRestB Wp Φ N inp p s r (.str t) t ρ H o rv Mp q ∗ ms 0x800030fc#64 R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hq0 : q ≠ 0#64 := fun h => f.hfresh.1.nonzero (by rw [h]; rfl)
  have hfr := f.hfresh.1
  have hq1 := hfr.lo; have hq2 := hfr.hi
  simp only [vsaLayoutP, Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd] at hq1 hq2
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := R) (Mt := M) (pc := 0x800030fc#64)
    (F := SgRestB Wp Φ N inp p s r (.str t) t ρ H o rv Mp q)
  rotate_left
  · unfold SgRestB
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine sg_scopy cx.hlive f.h2 (by omega) hs2 hs3 cx.hg.al
    (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi
    (by rw [f.h10]; exact hq0) ?_
  intros; apply swp_closeF
  dsimp only [F']
  rw [f.sn]
  unfold SgRestB
  iintro ⟨⟨#Hcode, #Himg, #Hv, Hh, Hblk, Hstd, Hcon, Hst, Hk⟩, Hms⟩
  ihave #Hs := valImg_str_strAt $$ Hv
  unfold strAt
  icases Hs with ⟨%img, %⟨hci, hw⟩, #Hro⟩
  ihave #Hmc0 := hmcr $$ Himg
  unfold memcpySpec
  ihave #Hmcs := Hmc0 $$ %q %(imgW (imgM Mp) (p.toNat + 8)) %(t.toList.length + 1) %img
  unfold memcpyPC
  iapply (ms_callRegs Wp (i := 0x8000310c)
    (jalx_8000310c live (fun q hq => cx.hlive _ (interp_code_8000310c q hq))) interp_code_8000310c
    (L := [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31])
    (K := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27])
    (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin q.toNat (t.toList.length + 1) ∧
        htifLo + 16 ≤ q.toNat ∧
        RamWin (imgW (imgM Mp) (p.toNat + 8)).toNat (t.toList.length + 1)⌝ ∗
      (10 : Nat) ↦ᵣ q ∗ (11 : Nat) ↦ᵣ imgW (imgM Mp) (p.toNat + 8) ∗
      (12 : Nat) ↦ᵣ BitVec.ofNat 64 (t.toList.length + 1) ∗ clobbered argClob ∗
      blockOwn q.toNat (t.toList.length + 1) ∗
      roImg (InExt ((imgW (imgM Mp) (p.toNat + 8)).toNat, t.toList.length + 1)) img))
    (Q := fun _ => iprop((10 : Nat) ↦ᵣ q ∗ clobbered retClob ∗
      ownImg (InExt (q.toNat, t.toList.length + 1))
        (fun a => img (a - q.toNat + (imgW (imgM Mp) (p.toNat + 8)).toNat))))
    (X := iprop(blockOwn q.toNat (t.toList.length + 1) ∗
      roImg (InExt ((imgW (imgM Mp) (p.toNat + 8)).toNat, t.toList.length + 1)) img))
    (Y := fun g => iprop(⌜g 10 = q⌝ ∗ ownImg (InExt (q.toNat, t.toList.length + 1))
        (fun a => img (a - q.toNat + (imgW (imgM Mp) (p.toNat + 8)).toNat))))
    (R := upd (upd (upd R 11 (imgW (imgM Mp) (p.toNat + 8))) 8 (R 10)) 12 (R 9))
    (S := sgF s p) (Mt := M) ?hP ?hQ)
  case hP =>
    simp only [sepL_cons, sepL_nil]
    iintro ⟨⟨H10, H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩, Hbk, #Hr⟩
    iframe Hbk Hr
    isplitl []
    · ipureintro
      have w1 := hw.lo; have w2 := hw.hi; have w3 := hw.htif
      refine ⟨by decide, ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩,
        by unfold htifLo; omega, ⟨by omega, by omega, by omega⟩⟩
    isplitl [H10]
    · ix_reg; rw [f.h10]; iexact H10
    isplitl [H11]
    · ix_reg; iexact H11
    isplitl [H12]
    · ix_reg; rw [f.h9]; iexact H12
    iapply clobbered_of_fn argClob _
    unfold argClob
    simp only [sepL_cons, sepL_nil]
    iframe H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31
  case hQ =>
    iintro ⟨H10, Hcl, Hd⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn retClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then q else g y)
    unfold retClob argClob
    simp only [sepL_cons, sepL_nil]
    icases Hcl with ⟨H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩
    simp only [ite_true]
    simp (config := { decide := true }) only [ite_false]
    iframe H10 H11 H12 H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31 Hd
  iframe Hmcs Hcode Hms Hblk Hro
  iintro %g ⟨%hg10, Hd⟩ Hms
  iapply sg_finish Wp cx (img := fun a => img (a - q.toNat + (imgW (imgM Mp) (p.toNat + 8)).toNat))
    (R := upd (fun y => if y ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] then g y else
      upd (upd (upd R 11 (imgW (imgM Mp) (p.toNat + 8))) 8 (R 10)) 12 (R 9) y) 1
      (BitVec.ofNat 64 (0x8000310c + 4))) (M := M)
    ⟨by simp [upd, f.h10], by simp [upd, f.h2], fun y hy hc' hy2 hy8 hy9 => by
        have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
        have hK : y ∉ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] := fun h => hc' ((show ∀ z ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31],
          z ∈ callerSaved by decide) y h)
        have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc' (e ▸ hz)
        simp only [upd, hy1, hK, hy8, hcl 11 (by decide), hcl 12 (by decide), ite_false]
        exact f.hk y hy hc' hy2 hy9,
      f.sra, f.ss0, f.ss1, f.hslot, cstrImg_shift hci, f.hfresh⟩ _ (.inr rfl)
  unfold SgRestC
  iframe Hcode Hv Hh Hd Hstd Hcon Hst Hk Hms

/-- **`malloc(len + 1)`** in the string arm, then the out-of-memory abort or
the copy. -/
theorem sg_strMalloc (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {x : String} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmcr : binImg (GF := GF) ⊢ memcpySpec Wp) (hc : vsaChg (x.toList.length + 1) c)
    (hlt : x.toList.length + 1 < 2 ^ 64)
    {R : Nat → BitVec 64} {M : Mem} (f : SgS2 s p r (imgW (imgM Mp) (p.toNat + 8)) x rv R M Mp) :
    SgRest Wp Φ N inp p s r (.str x) x ρ H c o rv Mp ∗
      ms 0x800030f8#64 R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have e112 : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
    rw [BitVec.toNat_add]; simp; omega
  have hn : stringifyNeed - 112 ≤ (s + 18446744073709551504#64).toNat := by
    rw [e112]; unfold stringifyNeed snprintfNeed; omega
  have hm : allocHeadroom ≤ stringifyNeed - 112 := by unfold allocHeadroom stringifyNeed snprintfNeed; omega
  iintro ⟨Hrest, Hms⟩
  unfold SgRest
  icases Hrest with ⟨#Hcode, #Himg, #Hat, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hn hm $$ Hst
  rw [← f.h2]
  iapply (ms_callMalloc A Wp (i := 0x800030f8)
    (jalx_800030f8 live (fun q hq => cx.hlive _ (interp_code_800030f8 q hq))) interp_code_800030f8
    (by decide) ρ H c (R := R) (by rw [f.h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact hc)
    ⟨by rw [f.h2, e112]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega,
      by rw [f.h2, e112]; omega, by rw [f.h2, e112]; omega⟩)
  iframe Hat Hcode Hms Hst Hh
  iintro %R' %hk' Hst Hres Hms
  rw [f.h2]
  ihave Hst := stackScratch_widen hn hm $$ [Hslack Hst]
  · iframe Hslack Hst
  rw [f.h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have k' : ∀ y ∈ fRegs, y ∉ callerSaved → R' y = R y := fun y hy hc => hk' y hy hc
  unfold mallocRes
  icases Hres with (⟨%⟨h0, hρ⟩, Hh⟩ | ⟨%hf, Hh, Hb⟩)
  · subst hρ
    iapply sg_oomPath Wp HN cx rfl (c := c) (pc := 0x800030fc) (.inr rfl)
      (R := upd R' 1 (BitVec.ofNat 64 (0x800030f8 + 4))) (M := M)
      (by ix_reg; rw [k' 2 (by decide) (by decide)]; exact f.h2) (by ix_reg; exact h0)
    unfold SgRest
    rw [Regime.plus_uncounted]
    iframe Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms
  · iapply sg_strCopy Wp cx hmcr (q := R' 10) (R := upd R' 1 (BitVec.ofNat 64 (0x800030f8 + 4)))
      (M := M) (f := ⟨by ix_reg, by ix_reg; rw [k' 9 (by decide) (by decide)]; exact f.h9,
        by ix_reg; rw [k' 2 (by decide) (by decide)]; exact f.h2,
        fun y hy hc hy2 hy9 => by
          have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
          simp only [upd, hy1, ite_false]
          rw [k' y hy hc]; exact f.hk y hy hc hy2 hy9,
        f.sra, f.ss0, f.ss1, f.sn, f.hslot, hf⟩)
    unfold SgRestB
    iframe Hcode Himg Hv Hh Hb Hstd Hcon Hst Hk Hms

/-- **A string**: `strlen`, `malloc`, `memcpy` of the payload, the return. -/
theorem sg_strArm (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hsl : binImg (GF := GF) ⊢ strlenSpec Wp) (hmcr : binImg (GF := GF) ⊢ memcpySpec Wp) {t : String}
    (hc : vsaChg (t.toList.length + 1) c) (hlt : t.toList.length + 1 < 2 ^ 64) {M : Mem}
    (hk : ldv .lw M p.toNat = 3#64) (hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k) :
    SgRest Wp Φ N inp p s r (.str t) t ρ H c o rv Mp ∗
      ms stringifyPC (upd rv 1 r) (sgF s p) M ⊢ Wp.W Φ :=
  sg_strHead Wp cx hsl hk hslot fun _ _ f2 => sg_strMalloc Wp A HN cx hmcr hc hlt f2

/-- A closure's arm entry (`0x8000301c`): the prologue's frame words saved,
the value's slot untouched. -/
structure SgC0 (s p r : BitVec 64) (rv R : Nat → BitVec 64) (M Mp : Mem) : Prop where
  h10 : R 10 = p
  h2 : R 2 = s + 18446744073709551504#64
  hk : ∀ y ∈ fRegs, y ∉ callerSaved → y ≠ 2 → R y = rv y
  sra : ldv .ld M (s + 18446744073709551504#64 + 104#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551504#64 + 96#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551504#64 + 88#64).toNat = rv 9
  hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k

/-- The closure object's and name field's facts the arm's loads need. -/
structure SgClo (M Dt : Mem) (p : BitVec 64) (cp q nm : Nat) : Prop where
  hw8 : ldv .ld M (p + 8#64).toNat = BitVec.ofNat 64 cp
  hc0 : ReadOK cp
  hc7 : ReadOK (cp + 7)
  hq : ldv .ld Dt cp = BitVec.ofNat 64 q
  hq0 : ReadOK (q + 8)
  hq7 : ReadOK (q + 15)
  hnm : ldv .ld Dt (q + 8) = BitVec.ofNat 64 nm
  hcp : cp < 2 ^ 64
  hql : q + 8 < 2 ^ 64

/-- **An anonymous closure**: `"<fn>"` stored inline, then the shared tail. -/
theorem sg_cloAnon (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hc : vsaChg ("<fn>".toList.length + 1) c)
    {Dt : Mem} {cp q : Nat} {R : Nat → BitVec 64} {M : Mem} (f0 : SgC0 s p r rv R M Mp)
    (fc : SgClo M Dt p cp q 0) :
    roOwn roR (interpText ++ dataOf Dt (clodA cp q)) ∗
      SgRest Wp Φ N inp p s r v "<fn>" ρ H c o rv Mp ∗ ms 0x8000301c#64 R (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hoff := sg_offs (s := s) (by omega)
  have hsep := cx.sep
  have e16 : (s + 18446744073709551504#64 + 16#64).toNat = s.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have e20 : (s + 18446744073709551504#64 + 16#64 + 4#64).toNat = s.toNat - 96 + 4 := by
    rw [BitVec.toNat_add, e16]; simp; omega
  iintro ⟨#Hview, Hrest, Hms⟩
  iapply wp_swpF Wp (text := interpText ++ dataOf Dt (clodA cp q)) (S := sgF s p) (R := R)
    (Mt := M) (pc := 0x8000301c#64) (F := SgRest Wp Φ N inp p s r v "<fn>" ρ H c o rv Mp)
  rotate_left
  · iframe Hview Hrest Hms
  intro F'
  refine sg_cloA cx.hlive f0.h10 f0.h2 (by omega) hs2 hs3 cx.hg.al
    (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi fc.hw8 fc.hc0 fc.hc7
    fc.hq fc.hq0 fc.hq7 fc.hnm fc.hcp fc.hql ?_
  intros; apply swp_closeF
  dsimp only [F']
  refine sg_tail Wp A HN cx hmc hc ⟨by ix_reg, by ix_reg, by ix_reg; exact f0.h2, ?_, ?_, ?_, ?_, ?_,
    by rw [e20, e16]; exact cstr_fn _ _, by decide⟩
  · intro y hy hc' hy2 hy9
    have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
    have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc' (e ▸ hz)
    simp only [upd, hy9, hcl 10 (by decide), hcl 13 (by decide), hcl 15 (by decide), ite_false]
    exact f0.hk y hy hc' hy2
  · rw [e20, e16, hoff 104 (by omega)]
    simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss]
    rw [← hoff 104 (by omega)]; exact f0.sra
  · rw [e20, e16, hoff 96 (by omega)]
    simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss]
    rw [← hoff 96 (by omega)]; exact f0.ss0
  · rw [e20, e16, hoff 88 (by omega)]
    simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss]
    rw [← hoff 88 (by omega)]; exact f0.ss1
  · intro k hk
    simp only [InExt] at hk
    rw [e20, e16]
    simp (disch := omega) only [imgM_store_miss]
    exact f0.hslot k (by simp only [InExt]; omega)

/-- **A named closure**: `snprintf(buf, 64, "<fn %s>", name)`
(`Sym.snprintfFn_out`), then the shared tail. -/
theorem sg_cloNamed (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {v : Value} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (Hout : OutHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) {x : String}
    (hc : vsaChg ((fnRender x).toList.length + 1) c)
    {Dt : Mem} {cp q nm : Nat} {R : Nat → BitVec 64} {M : Mem} (f0 : SgC0 s p r rv R M Mp)
    (fc : SgClo M Dt p cp q nm) (hnz : BitVec.ofNat 64 nm ≠ 0#64) :
    roOwn roR (interpText ++ dataOf Dt (clodA cp q)) ∗ strAt (BitVec.ofNat 64 nm).toNat x ∗
      SgRest Wp Φ N inp p s r v (fnRender x) ρ H c o rv Mp ∗ ms 0x8000301c#64 R (sgF s p) M ⊢
      Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have eB : (s + 18446744073709551504#64 + 16#64).toNat = s.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have e112 : (s + 18446744073709551504#64).toNat = s.toNat - 112 := by
    rw [BitVec.toNat_add]; simp; omega
  have hsl : ∀ k, sgF s p k ↔ (sgFnb s p k ∨ InExt (s.toNat - 96, 64) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (s.toNat - 96, 64) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact .inl (by simp only [InExt] at h ⊢; omega)
  have hlen : (fnRender x).toList.length ≤ 63 := by
    unfold fnRender; simp; omega
  iintro ⟨#Hview, #Hx, Hrest, Hms⟩
  iapply wp_swpF Wp (text := interpText ++ dataOf Dt (clodA cp q)) (S := sgF s p) (R := R)
    (Mt := M) (pc := 0x8000301c#64)
    (F := iprop(strAt (BitVec.ofNat 64 nm).toNat x ∗ SgRest Wp Φ N inp p s r v (fnRender x) ρ H c o rv Mp))
  rotate_left
  · iframe Hview Hx Hrest Hms
  intro F'
  refine sg_cloN cx.hlive f0.h10 f0.h2 (by omega) hs2 hs3 cx.hg.al
    (by have := cx.hg.lo; unfold Vsa.Sim.tohostAddr at this; omega) cx.hg.hi fc.hw8 fc.hc0 fc.hc7
    fc.hq fc.hq0 fc.hq7 fc.hnm hnz fc.hcp fc.hql ?_
  intros; apply swp_closeF
  dsimp only [F']
  iintro ⟨⟨#Hx, Hrest⟩, Hms⟩
  ihave Hms := ms_iff hsl $$ Hms
  ihave ⟨Hms, HB⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  ihave HB := ownSet_forget _ _ $$ HB
  unfold SgRest
  icases Hrest with ⟨#Hcode, #Himg, #Hat, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
  ihave #Hgp := codeRes_gp $$ Hcode
  have hsg' : SpIn (s + 18446744073709551504#64) snprintfNeed :=
    ⟨by rw [e112]; unfold snprintfNeed Vsa.Sim.tohostAddr; omega, by rw [e112]; omega,
      by rw [e112]; omega⟩
  ihave #Hsp := snprintfFn_out live Wp (s + 18446744073709551504#64)
    (s + 18446744073709551504#64 + 16#64) (BitVec.ofNat 64 nm) x (upd (upd (upd (upd (upd (upd (upd (upd R 15 (BitVec.ofNat 64 cp)) 15 (BitVec.ofNat 64 q)) 13
      (BitVec.ofNat 64 nm)) 9 (s + 18446744073709551504#64 + 16#64))
      10 (s + 18446744073709551504#64 + 16#64)) 12 2147586100#64) 12 2147586760#64) 11 64#64) cx.hcl hsg'
    (by rw [e112]; unfold snprintfNeed; omega) (by rw [eB]; omega) (by rw [eB]; omega)
  unfold snprintfFnSpec
  rw [eB]
  iapply (ms_callNewlibA Wp (i := 0x80003040)
    (jalx_80003040 live (fun q hq => cx.hlive _ (interp_code_80003040 q hq))) interp_code_80003040
    (vs := [s + 18446744073709551504#64 + 16#64, 64#64, 0x800192c8#64, BitVec.ofNat 64 nm])
    (P := fun ra0 => iprop(⌜ra0.toNat % 4 = 0⌝ ∗ argsAt [s + 18446744073709551504#64 + 16#64, 64#64, 0x800192c8#64,
        BitVec.ofNat 64 nm] ∗ blockOwn (s.toNat - 96) 64 ∗ strAt (BitVec.ofNat 64 nm).toNat x ∗
      stdioOwn ∗ callFrame (s + 18446744073709551504#64) snprintfNeed Newlib.calleeSaved
        (upd (upd (upd (upd (upd (upd (upd (upd R 15 (BitVec.ofNat 64 cp)) 15 (BitVec.ofNat 64 q)) 13
      (BitVec.ofNat 64 nm)) 9 (s + 18446744073709551504#64 + 16#64))
      10 (s + 18446744073709551504#64 + 16#64)) 12 2147586100#64) 12 2147586760#64) 11 64#64)))
    (Q := fun _ => iprop(clobbered argRegs ∗
      (∃ img, ownImg (InExt (s.toNat - 96, 64)) img ∗ ⌜CStrImg img (s.toNat - 96) (fnRender x)⌝) ∗
      stdioOwn ∗ callFrame (s + 18446744073709551504#64) snprintfNeed Newlib.calleeSaved
        (upd (upd (upd (upd (upd (upd (upd (upd R 15 (BitVec.ofNat 64 cp)) 15 (BitVec.ofNat 64 q)) 13
      (BitVec.ofNat 64 nm)) 9 (s + 18446744073709551504#64 + 16#64))
      10 (s + 18446744073709551504#64 + 16#64)) 12 2147586100#64) 12 2147586760#64) 11 64#64)))
    (X := iprop(blockOwn (s.toNat - 96) 64 ∗ strAt (BitVec.ofNat 64 nm).toNat x ∗ stdioOwn))
    (Y := iprop((∃ img, ownImg (InExt (s.toNat - 96, 64)) img ∗
      ⌜CStrImg img (s.toNat - 96) (fnRender x)⌝) ∗ stdioOwn))
    (need := snprintfNeed) (n := stringifyNeed - 112) (s := s + 18446744073709551504#64)
    (R := upd (upd (upd (upd (upd (upd (upd (upd R 15 (BitVec.ofNat 64 cp)) 15 (BitVec.ofNat 64 q)) 13
      (BitVec.ofNat 64 nm)) 9 (s + 18446744073709551504#64 + 16#64))
      10 (s + 18446744073709551504#64 + 16#64)) 12 2147586100#64) 12 2147586760#64) 11 64#64) (S := sgFnb s p)
    (by simp) (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | _ | _ | j
      · simp [upd]
      · simp [upd]
      · simp [upd]
      · simp [upd]
      · omega)
    (by simp [upd, f0.h2]) (by rw [e112]; unfold stringifyNeed snprintfNeed; omega)
    (by unfold stringifyNeed; omega) (by decide)
    (fun _ hr => by
      iintro ⟨Ha, ⟨Hb, Hs, Hio⟩, Hf⟩
      isplitr
      · ipureintro; exact hr
      iframe Ha Hb Hs Hio Hf)
    (fun _ => by iintro ⟨Ha, Hd, Hs, Hf⟩; iframe Ha Hd Hs Hf))
  unfold blockOwn snprintfEntry
  iframe Hsp Hcode Hms HB Hx Hstd Hst Hgp Himg
  iintro %R' %hk' ⟨Hd, Hstd⟩ Hms Hst
  have k' : ∀ y ∈ fRegs, y ∉ callerSaved → R' y = _ := fun y hy hc' => hk' y hy hc'
  iapply sg_filled Wp A HN cx hmc hc hlen (pc := 0x80003044#64) (.inr (.inr rfl))
    (R := upd R' 1 (BitVec.ofNat 64 (0x80003040 + 4))) (M := M)
    ⟨by ix_reg; rw [k' 9 (by decide) (by decide)]; simp [upd],
      by ix_reg; rw [k' 2 (by decide) (by decide)]; simp [upd, f0.h2],
      fun y hy hc' hy2 hy9 => by
        have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
        have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc' (e ▸ hz)
        simp only [upd, hy1, ite_false]
        rw [k' y hy hc']
        simp only [upd, hy9, hcl 10 (by decide), hcl 11 (by decide), hcl 12 (by decide),
          hcl 13 (by decide), hcl 15 (by decide), ite_false]
        exact f0.hk y hy hc' hy2,
      f0.sra, f0.ss0, f0.ss1, f0.hslot⟩
  unfold SgRest
  iframe Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms Hd

/-- `strRender` of a closure: its name cut, or `"<fn>"`. -/
theorem strRender_clos {st : Store} {ca : Nat} {cd : ClosureData} (hcd : st.closures[ca]? = some cd) :
    strRender st (.closure ca) = match cd.name with | some x => fnRender x | none => "<fn>" := by
  cases h : cd.name with
  | some x => simp [strRender, closName, hcd, h]
  | none => simp [strRender, closName, hcd, h, Value.catDisplay, Value.display]

/-- **A closure**: the object's `EX_FN` node and its name field through a data
view (`dispRes`, as `value_print`), then the named or anonymous path. -/
theorem sg_cloArm (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (Hout : OutHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) {ca : Nat} {st : Store}
    (hc : vsaChg ((strRender st (.closure ca)).toList.length + 1) c) {M : Mem}
    (hk : ldv .lw M p.toNat = 4#64) (hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k) :
    dispRes st (.closure ca) ∗
      SgRest Wp Φ N inp p s r (.closure ca) (strRender st (.closure ca)) ρ H c o rv Mp ∗
      ms stringifyPC (upd rv 1 r) (sgF s p) M ⊢ Wp.W Φ := by
  have hs1 := cx.hs1; have hs2 := cx.hs2; have hs3 := cx.hs3
  unfold stringifyNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff := sg_offs (s := s) (by omega)
  have hsep := cx.sep
  have hp1 := cx.hg.al; have hp2 := cx.hg.lo; have hp3 := cx.hg.hi
  unfold Vsa.Sim.tohostAddr at hp2
  have ep8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  iintro ⟨#Hd, Hrest, Hms⟩
  iapply wp_swpF Wp (S := sgF s p) (R := upd rv 1 r) (Mt := M) (pc := stringifyPC)
    (F := iprop(dispRes st (.closure ca) ∗
      SgRest Wp Φ N inp p s r (.closure ca) (strRender st (.closure ca)) ρ H c o rv Mp))
  rotate_left
  · unfold SgRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hd Hrest Hms
  intro F'
  refine sg_cloH cx.hlive cx.h10 cx.h2 (by omega) hs2 hs3 hp1 (by omega) hp3 hk ?_
  intros; apply swp_closeF
  dsimp only [F']
  iintro ⟨⟨#Hd, Hrest⟩, Hms⟩
  unfold SgRest
  icases Hrest with ⟨#Hcode, #Himg, #Hat, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
  ihave #Hd2 := dispRes_clos $$ Hd
  icases Hd2 with ⟨%cd, %cp, %q, %img, %P, %m, %⟨hcd, hqimg, hcR, hrep, hPR, hPW⟩, #Hca, #Hro, #Hon⟩
  ihave #Hca' := valImg_clos $$ Hv
  ihave %hcp := closAt_agree ca cp (imgW (imgM Mp) (p.toNat + 8)).toNat $$ [Hca Hca']
  · iframe Hca Hca'
  obtain ⟨w, hrw, hcov, hname⟩ := fnName_facts hrep
  have hP : ∀ k, q + 8 ≤ k → k < q + 16 → P k ∧ (m[k]?).isSome := fun k h1 h2 => by
    refine ⟨by have := hcov (k - (q + 8)) (by omega); rwa [show q + 8 + (k - (q + 8)) = k by omega] at this, ?_⟩
    have := read64_bytes_present hrw (k - (q + 8)) (by omega)
    rw [show q + 8 + (k - (q + 8)) = k by omega] at this
    rw [this]; rfl
  ihave ⟨%Dt, #Hview, %⟨hc', hn⟩⟩ := roOwn_clod hP $$ [Hcode Hro Hon]
  · iframe Hcode Hro Hon
  have hq0 := hPR (q + 8) (by have := hcov 0 (by omega); simpa using this)
  have hq01 := hq0.lo; have hq02 := hq0.hi
  have hcpl : cp < 2 ^ 64 := by rw [hcp]; exact (imgW (imgM Mp) (p.toNat + 8)).isLt
  have fc : SgClo (writeLog (writeLog (writeLog M
      [((s + 18446744073709551504#64 + 104#64).toNat, 8, r)])
      [((s + 18446744073709551504#64 + 96#64).toNat, 8, rv 8)])
      [((s + 18446744073709551504#64 + 88#64).toNat, 8, rv 9)]) Dt p cp q w := {
    hw8 := by
      rw [ep8, hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
      simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss]
      rw [ldv_ld_imgW, imgW_agree (g := imgM Mp) (fun j hj => hslot _ (by simp only [InExt]; omega)),
        hcp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    hc0 := hcR cp (by simp [InExt])
    hc7 := hcR (cp + 7) (by simp [InExt])
    hq := by
      rw [ldv_ld_imgW]; unfold imgW
      rw [imgLE_congr (img' := img) (fun i hi => hc' (cp + i) (by omega) (by omega)), hqimg]
    hq0 := hq0
    hq7 := hPR (q + 15) (by have := hcov 7 (by omega); simpa using this)
    hnm := by
      rw [ldv_ld_imgW]; unfold imgW
      have h8 : readLE m (q + 8) 8 = some (imgLE (imgM Dt) (q + 8) 8) :=
        readLE_of_img (fun i hi => hn (q + 8 + i) (by omega) (by omega))
      have : read64 m (q + 8) = readLE m (q + 8) 8 := rfl
      rw [this, h8] at hrw
      cases hrw; rfl
    hcp := hcpl
    hql := by omega }
  have f0 : SgC0 s p r rv (upd (upd (upd (upd (upd (upd rv 1 r) 15 4#64) 2
      (s + 18446744073709551504#64)) 14 3#64) 14 2#64) 14 4#64)
      (writeLog (writeLog (writeLog M
      [((s + 18446744073709551504#64 + 104#64).toNat, 8, r)])
      [((s + 18446744073709551504#64 + 96#64).toNat, 8, rv 8)])
      [((s + 18446744073709551504#64 + 88#64).toNat, 8, rv 9)]) Mp := by
    refine ⟨by simp [upd, cx.h10], by simp [upd], fun y hy hc'' hy2 => ?_, ?_, ?_, ?_, fun k hk => ?_⟩
    · have hy1 : y ≠ 1 := fun e => by subst e; revert hy; decide
      have hcl : ∀ z ∈ callerSaved, y ≠ z := fun z hz e => hc'' (e ▸ hz)
      simp [upd, hy1, hy2, hcl 14 (by decide), hcl 15 (by decide)]
    all_goals first
      | (simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
         simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit])
      | (simp only [InExt] at hk
         simp only [hoff 104 (by omega), hoff 96 (by omega), hoff 88 (by omega)]
         simp (disch := omega) only [imgM_store_miss]
         exact hslot k (by simp only [InExt]; omega))
  rw [strRender_clos hcd] at hc ⊢
  rcases hname with ⟨hn0, rfl⟩ | ⟨x, hnx, hnz, hcs⟩
  · rw [hn0] at hc ⊢
    iapply sg_cloAnon Wp A HN cx hmc hc f0 fc
    unfold SgRest
    iframe Hview Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms
  · rw [hnx] at hc ⊢
    ihave #Hx := strAt_of_cstringWithin hcs hPW $$ Hon
    have hwl := read64_lt hrw
    iapply sg_cloNamed Wp A HN Hout cx hmc hc f0 fc (fun h => hnz (by
      have := congrArg BitVec.toNat h; simp at this; omega))
    rw [show (BitVec.ofNat 64 w).toNat = w by simp; omega]
    unfold SgRest
    iframe Hview Hx Hcode Himg Hat Hv Hh Hstd Hcon Hst Hk Hms

omit G in
/-- A string value's length fits a word (its payload's `StrWin`). -/
theorem valImg_strLen [MachGS hlc GF] {N : NativeAddrs} {img : Nat → BitVec 8} {a : Nat}
    {v : Value} : valImg (GF := GF) N img a v ⊢
      ⌜∀ t, v = .str t → t.toList.length + 1 < 2 ^ 64⌝ := by
  cases v
  case str t =>
    iintro #H
    ihave #Hs := valImg_str_strAt $$ H
    ihave %hw := strAt_win $$ Hs
    ipureintro
    intro t' ht'
    cases ht'
    have := hw.hi
    omega
  all_goals
    iintro -
    ipureintro
    intro t h
    cases h

/-- The kind dispatch at `stringify`'s entry: each kind's arm. -/
theorem sg_dispatch (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {p s r : BitVec 64} {st : Store} {ρ : Regime}
    {H : List (Nat × Nat)} {c : Nat} {o : String} {rv : Nat → BitVec 64} {Mp : Mem}
    (A : AllocSpecs live) (HN : NewlibHoles) (Hout : OutHoles) (cx : SgCtx live p s r rv)
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hmcr : binImg (GF := GF) ⊢ memcpySpec Wp)
    (hsl : binImg (GF := GF) ⊢ strlenSpec Wp) (hsc : binImg (GF := GF) ⊢ strcpySpec (vsaModel live) Wp) {v : Value}
    (hc : vsaChg ((strRender st v).toList.length + 1) c)
    (hpv : ValPure N v (imgW (imgM Mp) p.toNat) (imgW (imgM Mp) (p.toNat + 8))
      (imgW (imgM Mp) (p.toNat + 16)))
    (hlt : ∀ t, v = .str t → t.toList.length + 1 < 2 ^ 64) {M : Mem}
    (hslot : ∀ k, InExt (p.toNat, 24) k → imgM M k = imgM Mp k) :
    dispRes st v ∗ SgRest Wp Φ N inp p s r v (strRender st v) ρ H c o rv Mp ∗
      ms stringifyPC (upd rv 1 r) (sgF s p) M ⊢ Wp.W Φ := by
  have hp3 := cx.hg.hi
  have hkind : ldv .lw M p.toNat = BitVec.ofNat 64 (Vsa.RuntimeRepr.kindTag v) := by
    refine ldv_lw_kind ?_ (kindTag_small _)
    rw [imgW_agree (g := imgM Mp) (fun j hj => hslot _ (by simp only [InExt]; omega))]
    exact hpv.kind
  have e8 : (p + 8#64).toNat = p.toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (show p.toNat + 8 < 2 ^ 64 by omega)]
  have hw8 : ∀ k, (imgW (imgM Mp) (p.toNat + 8)).toNat % 2 ^ 32 = k → k < 2 ^ 31 →
      ldv .lw M (p + 8#64).toNat = BitVec.ofNat 64 k := by
    intro k hk hk'
    rw [e8]
    refine ldv_lw_kind ?_ hk'
    rw [imgW_agree (g := imgM Mp) (fun j hj => hslot _ (by simp only [InExt]; omega))]
    exact hk
  have hd8 : ldv .ld M (p + 8#64).toNat = imgW (imgM Mp) (p.toNat + 8) := by
    rw [e8, ldv_ld_imgW,
      imgW_agree (g := imgM Mp) (fun j hj => hslot _ (by simp only [InExt]; omega))]
  cases v with
  | null =>
    rw [show strRender st .null = "null" from rfl] at hc ⊢
    iintro ⟨-, HR⟩
    iapply sg_nullArm (st := st) Wp A HN cx hmc hc (by rw [hkind]; rfl) hslot
    iexact HR
  | bool b =>
    have hb : ldv .lw M (p + 8#64).toNat = if b then 1#64 else 0#64 := by
      rw [hw8 (cond b 1 0) hpv.2 (by cases b <;> decide)]
      cases b <;> rfl
    rw [show strRender st (.bool b) = (if b then "true" else "false") by cases b <;> rfl] at hc ⊢
    iintro ⟨-, HR⟩
    iapply sg_boolArm Wp A HN cx hmc hsc hc (by rw [hkind]; rfl) hb hslot
    iexact HR
  | int n =>
    rw [show strRender st (.int n) = intToString n from rfl] at hc ⊢
    obtain ⟨-, hn⟩ := hpv
    subst hn
    iintro ⟨-, HR⟩
    iapply sg_intArm Wp A HN Hout cx hmc hc (by rw [hkind]; rfl) hd8 hslot
    iexact HR
  | str t =>
    rw [show strRender st (.str t) = t from rfl] at hc ⊢
    iintro ⟨-, HR⟩
    iapply sg_strArm Wp A HN cx hsl hmcr hc (hlt t rfl) (by rw [hkind]; rfl) hslot
    iexact HR
  | closure ca =>
    exact sg_cloArm Wp A HN Hout cx hmc hc (by rw [hkind]; rfl) hslot
  | native f =>
    rw [show strRender st (.native f) = "<native fn>" from rfl] at hc ⊢
    iintro ⟨-, HR⟩
    iapply sg_natArm (st := st) (f := f) Wp A HN cx hmc hc (by rw [hkind]; rfl) hslot
    iexact HR

/-- **`stringify`**, for either WP: the rendering in a fresh heap block, or the
out-of-memory abort. `hstk`: the stack region is live (H3's `strlen` over the
stack buffer). -/
theorem stringify_spec (hlive : ∀ q ∈ interpText, live q.1) (hcl : CodeLive live)
    (hstk : ∀ a, 0x87800000 ≤ a → a < 0x88000000 → live a)
    (A : AllocSpecs live) (HN : NewlibHoles) (Hout : OutHoles)
    (Wp : MachWP (GF := GF) (vsaModel live))
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp) (hmcr : binImg (GF := GF) ⊢ memcpySpec Wp)
    (hsl : binImg (GF := GF) ⊢ strlenSpec Wp) (hsc : binImg (GF := GF) ⊢ strcpySpec (vsaModel live) Wp)
    (N : NativeAddrs) (inp : Nat) (p s : BitVec 64) (v : Value) (st : Store) (ρ : Regime)
    (H : List (Nat × Nat)) (c : Nat) (o : String) :
    textOwn allocText ⊢ stringifySpec (vsaModel live) N Wp inp p s v st ρ H c o := by
  unfold stringifySpec fnSpecAbort
  iintro #Htx %rv !> %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨h10, h2⟩, #Hcode, Hv, %⟨hg, hc⟩, #Hd, #Himg,
    Hh, Hstd, Hcon, ⟨Hst, %hsg⟩⟩ Hk
  have hs1 := hsg.le; have hs2 := hsg.lo; have hs3 := hsg.hi; have hs4 := hsg.al
  simp only [Vsa.Sim.LayoutInstance.stackSL] at hs2 hs3
  have hs0 : 0x87800000 + stringifyNeed ≤ s.toNat := by
    unfold stringifyNeed snprintfNeed at hs1 hs2 ⊢
    show 2273312768 + (112 + 1024) ≤ s.toNat
    omega
  ihave ⟨%Ma, HA, #Hw⟩ := valAt_tracked N _ v $$ Hv
  ihave %hpv := valOf_pure N v _ _ _ $$ Hw
  ihave %hlt := valImg_strLen $$ Hw
  ihave ⟨Hst, HF⟩ := sgFrame_split (s := s) hs1 $$ Hst
  ihave ⟨%f, HF⟩ := ownSet_fn _ $$ HF
  ihave ⟨%Mf, HF⟩ := ownSet_mem _ f $$ HF
  ihave ⟨%M, HM, %⟨-, hMa, hdsp⟩⟩ := ownSet_join_tracked _ _ Mf Ma $$ [HF HA]
  · iframe HF HA
  have cx : SgCtx live p s r rv := ⟨hlive, hcl, hstk, hal, h10, h2, hs0, hs3, hs4, hsg.top, hg, hdsp⟩
  have hms : ms (GF := GF) stringifyPC (upd rv 1 r) (sgF s p) M =
      iprop(PC ↦ᵣ stringifyPC ∗ ra ↦ᵣ r ∗ regFile rv ∗
        ownSet (fun a => InExt (s.toNat - 112, 112) a ∨ InExt (p.toNat, 24) a)
          (fun a => a ↦ₘ imgM M a)) := by
    unfold ms; rw [regFile_upd_ra]; simp only [upd_same]
  iapply sg_dispatch Wp A HN Hout cx hmc hmcr hsl hsc hc hpv hlt hMa
  unfold SgRest
  rw [hms]
  iframe Hd Hcode Himg Htx Hw Hh Hstd Hcon Hst Hk Hpc Hra Hregs HM

end Glue

end VsaIris.Interp

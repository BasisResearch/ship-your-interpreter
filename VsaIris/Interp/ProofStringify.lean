import VsaIris.Interp.SpecStringify
import VsaIris.Interp.CallRegs
import VsaIris.Interp.ProofNativeAssert
import VsaIris.Vsa.StrlenOwned

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
    (abortRes N vsaLayoutP vsaRoomB inp s stringifyNeed -∗ Wp.W Φ))

/-- What a `stringify` run carries: the value's meaning at its image, the heap,
newlib's data and the console, the stack below the frame, the continuation. -/
def SgRest (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (inp : Nat) (p s r : BitVec 64) (v : Value) (x : String) (ρ : Regime)
    (H : List (Nat × Nat)) (c : Nat) (o : String) (rv : Nat → BitVec 64) (Mp : Mem) : IProp GF :=
  iprop(codeRes ∗ binImg ∗ valImg N (imgM Mp) p.toNat v ∗
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
  hg : SlotGeom p
  hdsp : ∀ k, InExt (s.toNat - 112, 112) k → ¬ InExt (p.toNat, 24) k

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
  icases Hrest with ⟨#Hcode, #Himg, #Hv, Hh, Hstd, Hcon, Hst, Hk⟩
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
    iframe Hcode Himg Hv Hh Hstd Hcon Hst Hk Hms
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

end Glue

end VsaIris.Interp

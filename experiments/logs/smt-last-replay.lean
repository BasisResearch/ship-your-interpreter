import Vsa.Sim.TermAssembly
/-! UNCONTAMINATED fuzzer-v2 test: novel statements, same disease class,
FRESH parameters/names/shape variants the tool has never seen. -/
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

-- N1: FALSE, same class, novel window (a totally different range 0x90000..)
-- and novel demand (a *specific byte value* survives, not just presence).
def NovelResidA : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)) (base : BitVec 64),
    m0[(0x90000 : Nat)]? = some (0x2a : BitVec 8) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, ¬ (0x90000 ≤ k ∧ k < 0x90010) → m0[k]? = mq[k]?) →
      mq[(0x90000 : Nat)]? = some (0x2a : BitVec 8)

-- N2: TRUE variant (the cure shape at novel parameters): agreement ON the
-- window is demanded, so the adversary is excluded.
def NovelResidB : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    m0[(0x90000 : Nat)]? = some (0x2a : BitVec 8) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, (0x8f000 ≤ k ∧ k < 0x91000) → m0[k]? = mq[k]?) →
      mq[(0x90000 : Nat)]? = some (0x2a : BitVec 8)

-- N3: FALSE, shape VARIANT — two disjoint agree-windows, demand in the gap
-- between them (neither window covers it). Structurally new: conjunction of
-- two agree-hyps.
def NovelResidC : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    (∀ k, k < 0x100 → m0[k]? = some (0x1 : BitVec 8)) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, k < 0x100 → m0[k]? = mq[k]?) →
      (∀ k, 0x200 ≤ k → m0[k]? = mq[k]?) →
      ∀ a, 0x100 ≤ a ∧ a < 0x200 → mq[a]? = m0[a]?


namespace SmtReplay
set_option maxHeartbeats 1000000 in
theorem refuted : ¬ NovelResidA := by
  intro H
  have h := H ⟨8, 589834⟩ (8445486756382732986#64)
  simp only [NovelResidA] at h
  revert h
  decide
#print axioms refuted
end SmtReplay

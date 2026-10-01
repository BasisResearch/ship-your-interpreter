import VsaIris.Vsa.Fprintf.Tac
import VsaIris.Interp.Arm
import VsaIris.Vsa.MoveRun

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open scoped VsaIris.Sym.Stdout

macro "fp_hb " h:ident : tactic => `(tactic| simp only [mem_accAddrs_iff,
  LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
  BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow] at $h:ident)

scoped macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; fp_hb hb; nf_cover))

def ReadB (Dt : Mem) (DA : List Nat) (S : Nat → Prop) (Mt : Mem) (a : Nat) (b : BitVec 8) : Prop :=
  (a ∈ DA ∧ imgM Dt a = b) ∨ (S a ∧ imgM Mt a = b)

theorem ReadB.transport {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt Mt' : Mem} {a : Nat}
    {b : BitVec 8} (h : ReadB Dt DA S Mt a b) (hM : imgM Mt' a = imgM Mt a) : ReadB Dt DA S Mt' a b := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨h1, hM.trans h2⟩

def ReadWin (Dt : Mem) (DA : List Nat) (S : Nat → Prop) (Mt : Mem) (lo hi : Nat)
    (g : Nat → BitVec 8) : Prop :=
  ∀ a, lo ≤ a → a < hi → ReadB Dt DA S Mt a (g a)

theorem ReadWin.transport {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt Mt' : Mem} {lo hi : Nat}
    {g : Nat → BitVec 8} (h : ReadWin Dt DA S Mt lo hi g)
    (hM : ∀ a, lo ≤ a → a < hi → imgM Mt' a = imgM Mt a) : ReadWin Dt DA S Mt' lo hi g :=
  fun a h1 h2 => (h a h1 h2).transport (hM a h1 h2)

theorem imgM_sb_zext (Mt : Mem) (a : Nat) (b : BitVec 8) :
    imgM (writeLog Mt [(a, 1, BitVec.zeroExtend 64 b)]) a = b := by
  have h := pin1_of_writeLog Mt [] [] a (BitVec.zeroExtend 64 b) trivial
  simp only [List.nil_append] at h
  unfold imgM
  rw [h, Option.getD_some, sbData_zext]

structure Copied (Mt Mt0 : Mem) (d src c : Nat) (g : Nat → BitVec 8) : Prop where
  done : ∀ i, i < c → imgM Mt (d + i) = g (src + i)
  rest : ∀ a, a < d ∨ d + c ≤ a → imgM Mt a = imgM Mt0 a

theorem ofNat_add_ofNat (x y : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

abbrev MMFrame (R R0 : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 11 → z ≠ 12 → z ≠ 13 → z ≠ 14 → z ≠ 15 → z ≠ 16 → z ≠ 17 → z ≠ 6 → z ≠ 28 →
    R z = R0 z

syntax "rsimp" (Lean.Parser.Tactic.location)? : tactic
scoped macro_rules
  | `(tactic| rsimp $[$loc]?) =>
    `(tactic| simp (config := {failIfUnchanged := false}) only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] $[$loc]?)

theorem move_stdio : ∀ p ∈ moveText, p ∈ stdioText := fun p hp => List.mem_append_left _
  (piecesText_sub (rs' := stdioCodeRanges) (fun a h => by
    simp [inRangesB, moveRanges, stdioCodeRanges] at h ⊢; omega) p hp)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem memmove_run (hlive : ∀ p ∈ stdioText, live p.1) (d src len : Nat) (g : Nat → BitVec 8)
    (R : Nat → BitVec 64) (Mt : Mem) (G : MoveGeom S d src len)
    (hw : ReadWin Dt DA S Mt src (src + len) g)
    (h10 : R 10 = BitVec.ofNat 64 d) (h11 : R 11 = BitVec.ofNat 64 src)
    (h12 : R 12 = BitVec.ofNat 64 len) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', MMFrame R' R → Copied Mt' Mt d src len g → NW live Dt DA S Q (R 1) R' Mt') :
    NW live Dt DA S Q 0x800069c4#64 R Mt :=
  swp_host_out (fun p hp => List.mem_append_left _ (move_stdio p hp))
    (memmoveH (fun p hp => hlive _ (move_stdio p hp)) d src len g R Mt G h10 h11 h12 hal hw
      fun R' Mt' hF hc => swp_host_in (hk R' Mt' hF ⟨hc.1, hc.2⟩))

end VsaIris.Sym.Fp

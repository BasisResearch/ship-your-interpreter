import VsaIris.Vsa.HeapTake
import VsaIris.Vsa.AllocHoles
import VsaIris.Vsa.AllocTac
import VsaIris.Vsa.MallocFastChain

/-!
# `_malloc_r` on the general heap: entry, exit, and the tracking memory

A malloc run starts from the caller's owned values and the page-aligned
heap. `mallocChgRun_of_aw` reduces `MallocChgRun` at the binary to one `AW`
goal at `malloc`'s entry:

* the register file is the entry valuation;
* the tracking memory `mt0` is the heap witness `m1` with the stack window
  inserted.

`malloc_exit` closes a run at the return. The ABI frame restored, a fresh
block in `a0`, and the page-aligned heap with its credits on the tracking
memory give `MallocRoomEnd`. Every path of `_malloc_r` is a chain of step
lemmas between these two, through the join lemmas of `MallocPaths.lean`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- The bytes a malloc call owns at the binary. -/
abbrev mS (H : List (Nat × Nat)) (s : BitVec 64) : Nat → Prop :=
  mallocBytes vsaLayoutP H s allocHeadroom

/-- What a counted malloc run ends in. -/
abbrev mQ (H : List (Nat × Nat)) (n r s : BitVec 64) (saved : List (Nat × BitVec 64)) (k : Nat) :
    (Nat → BitVec 64) → (Nat → BitVec 8) → Prop :=
  MallocRoomEnd vsaLayoutP vsaRoomB H n r s saved k

/-- The tracking memory at entry: the heap witness with the stack window. -/
abbrev mt0 (m1 : Mem) (s : BitVec 64) (mv : Nat → BitVec 8) : Mem :=
  stackBase m1 (s.toNat - allocHeadroom) allocHeadroom mv

theorem aRegs_eq : aRegs = allocRegs vsaClob vsaSaved := rfl

/-- **`MallocChgRun` from the symbolic run at entry.** -/
theorem mallocChgRun_of_aw {live : Nat → Prop}
    (hrun : ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
      (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (k c : Nat) (m1 : Mem) (top brkv : Nat)
      (chunks : List Chunk) (bins : Nat → List Nat),
      saved.map Prod.fst = vsaSaved → vsaChg n.toNat c → SpOKA s → r.toNat % 4 = 0 →
      EntryRegs rv mallocEntryBV r n s saved →
      ImgOn (vsaFoot H) mv m1 → PHeapAt m1 H top brkv chunks bins →
      2 * (k + c) + extendSlack ≤ heapEnd - top →
      (∀ a, stackWin s allocHeadroom a → ¬ vsaFoot H a) →
      AW live (mS H s) (mQ H n r s saved k) mallocEntryBV rv (mt0 m1 s mv)) :
    MallocChgRun (vsaModel live) vsaLayoutP vsaRoomB vsaChg SpOKA mallocEntryBV gpV vsaClob vsaSaved
      allocHeadroom allocText := by
  intro H n s r saved rv mv k c hsv hchg hsp hral he _ hroom hdisj
  obtain ⟨m1, top, brkv, chunks, bins, him, hheap, hcap⟩ := hroom
  obtain ⟨fuel, hf⟩ := hrun H n s r saved rv mv k c m1 top brkv chunks bins hsv hchg hsp hral he
    him hheap hcap hdisj
  refine ⟨fuel, hf rv mv ⟨he.pc, fun _ _ _ => rfl, fun a ha => ?_⟩⟩
  unfold imgM mt0
  rw [stackBase_get]
  rcases ha with hs | hh
  · rw [ite_eq_left_iff.2 (fun h => absurd ⟨hs.1, by unfold stackWin InExt at hs; simp only at hs; omega⟩ h)]
    rfl
  · have hns : ¬ (s.toNat - allocHeadroom ≤ a ∧ a < s.toNat - allocHeadroom + allocHeadroom) :=
      fun h => hdisj a ⟨h.1, by simp only; omega⟩ hh
    rw [ite_eq_right_iff.2 (fun h => absurd h hns), him a hh]
    rfl

/-- **The return.** At the return address with the ABI frame restored, a
fresh aligned block in `a0` and the page-aligned heap with `k` credits on
the tracking memory, the run is done. -/
theorem malloc_exit {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {k : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hsv : saved.map Prod.fst = vsaSaved)
    (hra : R 1 = r) (hsp : R 2 = s) (hsaved : ∀ p ∈ saved, R p.1 = p.2)
    (hfresh : FreshBlock vsaLayoutP H (R 10).toNat n.toNat) (hal : (R 10).toNat % 16 = 0)
    (hheap : PHeapAt Mt (((R 10).toNat, n.toNat) :: H) top brkv chunks bins)
    (hcap : 2 * k + extendSlack ≤ heapEnd - top)
    (hpres : ∀ a, vsaFoot H a → (Mt[a]?).isSome) :
    AW live (mS H s) (mQ H n r s saved k) r R Mt := by
  refine swp_done fun rv mv hm => ?_
  have hreg : ∀ x ∈ aRegs, x ≠ VsaIris.PC → rv x = R x := hm.regs
  have hsub : ∀ a, vsaFoot (((R 10).toNat, n.toNat) :: H) a → vsaFoot H a := by
    rintro a (hg | ⟨h1, h2, h3⟩)
    · exact .inl hg
    · exact .inr ⟨h1, h2, fun e he => h3 e (List.mem_cons_of_mem _ he)⟩
  have ha0 : rv VsaIris.a0 = R 10 := hreg 10 (by decide) (by decide)
  have him : ImgOn (vsaFoot (((R 10).toNat, n.toNat) :: H)) mv Mt := by
    intro a ha
    have hp := hpres a (hsub a ha)
    rw [hm.img a (.inr (hsub a ha))]
    unfold imgM
    cases h : Mt[a]? with
    | none => rw [h] at hp; cases hp
    | some b => rfl
  refine ⟨⟨hm.pc, ?_, ?_, fun p hp => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [show VsaIris.ra = 1 from rfl, hreg 1 (by decide) (by decide), hra]
  · rw [show VsaIris.sp = 2 from rfl, hreg 2 (by decide) (by decide), hsp]
  · have hk : p.1 ∈ vsaSaved := by rw [← hsv]; exact List.mem_map_of_mem hp
    have hk' : p.1 ∈ aRegs ∧ p.1 ≠ VsaIris.PC := by
      unfold vsaSaved at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h | h | h | h <;> rw [h] <;> decide
    rw [hreg p.1 hk'.1 hk'.2, hsaved p hp]
  · rw [ha0]; exact hfresh
  · rw [ha0]; exact hal
  · rw [ha0]; exact ⟨Mt, top, brkv, chunks, bins, him, hheap⟩
  · rw [ha0]; exact ⟨Mt, top, brkv, chunks, bins, him, hheap, hcap⟩

end VsaIris.VsaHeap

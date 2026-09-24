import VsaIris.Interp.ExecDisp

/-!
# The exec arm layer (lane E5)

What every `exec_stmt` arm shares, from the dispatch point
(`SpecExecDisp.lean`): the statement node's reads (`StmtNode`, `stmtView`), the
frame geometry, the epilogues.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

/-- The bytes of a statement node a run reads: the tag word and the fields
from `+8` to `+w` (never the line field at `+4`). -/
abbrev stmtView (a w : Nat) : List Nat := accAddrs a 4 ++ accAddrs (a + 8) (w - 8)


/-- What a statement node gives the runs: its tag reads at the node's
register value, its placement (`w` bytes from the node), its view. -/
structure StmtNode (m : Mem) (P : Nat → Prop) (aS : BitVec 64) (tag w : Nat) : Prop where
  kind : ldv .lw m aS.toNat = BitVec.ofNat 64 tag
  kindu : ldv .lwu m aS.toNat = BitVec.ofNat 64 tag
  lo : 0x80000000 ≤ aS.toNat
  hi : aS.toNat + w ≤ 0x100000000
  off : aS.toNat + w ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat
  view : ∀ a ∈ stmtView aS.toNat w, P a ∧ (m[a]?).isSome
  geo : ∀ k, P k → Interp.ReadOK k

/-- A node's facts from its tag read and the reads of its fields `[+8, +w)`
(`w = 4`: the tag alone). -/
theorem stmtNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {tag w : Nat}
    (hg : ∀ k, P k → Interp.ReadOK k) (ht : read32 m aS.toNat = some tag) (hc : Covers P aS.toNat 4)
    (htag : tag < 2 ^ 31) (hw : w = 4 ∨ 9 ≤ w)
    (hmid : ∀ j, 8 ≤ j → j < w → P (aS.toNat + j) ∧ (m[aS.toNat + j]?).isSome) :
    StmtNode m P aS tag w := by
  have g0 := hg _ (hc 0 (by omega))
  have g3 := hg _ (hc 3 (by omega))
  have hlast : Interp.ReadOK (aS.toNat + (w - 1)) := by
    rcases hw with rfl | hw
    · exact g3
    · exact hg _ (hmid (w - 1) (by omega) (by omega)).1
  refine ⟨ldv_lw_read32 ht htag, ldv_lwu_read32 ht, by simpa using g0.lo, ?_, ?_, ?_, hg⟩
  · have := hlast.hi; omega
  · have h0 := g0.off; have h1 := hlast.off
    simp only [Nat.add_zero] at h0
    unfold Vsa.Sim.tohostAddr at *
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · left; omega
    · -- a byte of the node would sit on the HTIF words
      exfalso
      rcases hw with rfl | hw
      · omega
      have := (hg _ (hmid (2147593472 + 15 - aS.toNat) (by omega) (by omega)).1).off
      unfold Vsa.Sim.tohostAddr at this; omega
    · omega
    · right; omega
  · intro a ha
    simp only [List.mem_append, mem_accAddrs_iff] at ha
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + j := ⟨a - aS.toNat, by omega⟩
      exact ⟨hc j (by omega), isSome_of_readLE ht (by omega)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + j := ⟨a - aS.toNat, by omega⟩
      exact hmid j (by omega) (by omega)

/-- A field word of a placed node. -/
theorem field64 {m : Mem} {aS : BitVec 64} {o p : Nat} (hr : read64 m (aS.toNat + o) = some p)
    (hhi : aS.toNat + o + 8 ≤ 0x100000000) :
    ldv .ld m (aS + BitVec.ofNat 64 o).toNat = BitVec.ofNat 64 p := by
  have e : (aS + BitVec.ofNat 64 o).toNat = aS.toNat + o := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; exact ldv_ld_read64 hr

/-- The bytes of a field read, as the node view's middle. -/
theorem field_mid {m : Mem} {P : Nat → Prop} {a o n v : Nat} (hr : readLE m (a + o) n = some v)
    (hc : Covers P (a + o) n) {j : Nat} (h1 : o ≤ j) (h2 : j < o + n) :
    P (a + j) ∧ (m[a + j]?).isSome := by
  obtain ⟨i, rfl⟩ : ∃ i, j = o + i := ⟨j - o, by omega⟩
  rw [← Nat.add_assoc]
  exact ⟨hc i (by omega), isSome_of_readLE hr (by omega)⟩

section FrameRes

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **Leaving `exec_stmt`'s frame**: the frame bytes rejoin the stack below
the entry `sp`. -/
theorem execFrame_join {s : BitVec 64} {n : Nat} (hn : n ≤ s.toNat) (hf : 176 ≤ n) :
    stackScratch (GF := GF) (execSP s) (n - 176) ∗ ownSet (InExt (s.toNat - 176, 176)) byteAny ⊢
      stackScratch s n := by
  have e : (s - 176#64).toNat = s.toNat - 176 := toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have h := stackScratch_unframe (GF := GF) (s := s) (f := 176#64) (n := n) hn (by simp only [BitVec.toNat_ofNat]; omega)
  rw [e, show (176#64).toNat = 176 from rfl, execSP_eq] at h
  exact h

end FrameRes

section Finish

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **The end of an exec arm**, for either WP: after the epilogue's `ret`
(the machine state at the return address, `ra` holding it), the frame bytes
rejoin the stack and the dispatch-point continuation takes the rest. -/
theorem execDisp_finish (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {ρ : Regime} {st' : St} {d : Nat} {sm : Stmt} {status : Status} {aRet s ret : BitVec 64}
    {R R' : Nat → BitVec 64} {Mt : Mem} {v8 v9 v18 v19 pc : BitVec 64}
    (hsg : StackGeom s (execNeed sm d)) (hpc : pc = ret) (hra : R' 1 = ret)
    (hret : ExecRet R R' s v8 v9 v18 v19 status) :
    ms pc R' (InExt (s.toNat - 176, 176)) Mt ∗ stackScratch (execSP s) (execNeed sm d - 176) ∗
      statusRet N aRet.toNat status ∗ world N L Room inp ρ st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm status aRet s R ret v8 v9 v18 v19
    ⊢ Wp.W Φ := by
  obtain ⟨_, hneed⟩ := execFrameGeom_of hsg
  iintro ⟨Hms, Hst, Hret, Hw, HK⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := execFrame_join hsg.le hneed $$ [Hst HS]
  · iframe Hst HS
  rw [hpc, hra]
  unfold execDispK
  iapply HK $$ %R' %hret Hpc Hra Hregs Hst Hret Hw

end Finish

end VsaIris.Interp

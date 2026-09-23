import VsaIris.Vsa.MallocFastSegs

/-!
# `_malloc_r`'s top-split path for requests of at most 23 bytes, reflected

Requests `n ≤ 23` take the minimum chunk (`nb = 32`): the prologue skips the
size computation and the saved `nb` (`segProB`, ending at the lock call at
`0x800047cc`), and after the lock hook the bin checks start at bin 4 directly
(`segBinsB`, joining `segBins`' tail). From the top-size tests on, the path is
the larger requests' (`segSplit`, the unlock call, `segEpi`). Chains generated
by `scripts/emit_derive_case.py scripts/malloc_fast_segs.json`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Vsa.Sim

#derive_case segProB chain
  [(0x800047a8#64, 0xfa010113#32),
   (0x800047ac#64, 0x04813823#32),
   (0x800047b0#64, 0x04113c23#32),
   (0x800047b4#64, 0x01758713#32),
   (0x800047b8#64, 0x02e00793#32),
   (0x800047bc#64, 0x00050413#32)]
  terminator ⟨0x800047c0#64, 0x08e7ee63#32, 0x63#8, 0xee#8, 0xe7#8, 0x08#8,
      .br bop.BLTU false, 15, 14, 0x09c#13, 0#21, 0#12⟩ ;;
  [(0x800047c4#64, 0x02000713#32)]
  terminator ⟨0x800047c8#64, 0x06b76c63#32, 0x63#8, 0x6c#8, 0xb7#8, 0x06#8,
      .br bop.BLTU false, 14, 11, 0x078#13, 0#21, 0#12⟩

#derive_case segBinsB chain
  [(0x800047d0#64, 0x02000713#32),
   (0x800047d4#64, 0x05000693#32),
   (0x800047d8#64, 0x00400893#32),
   (0x800047dc#64, 0x00016817#32),
   (0x800047e0#64, 0x53480813#32),
   (0x800047e4#64, 0x00d806b3#32),
   (0x800047e8#64, 0x0086b783#32),
   (0x800047ec#64, 0xff068613#32)]
  terminator ⟨0x800047f0#64, 0x46c78863#32, 0x63#8, 0x88#8, 0xc7#8, 0x46#8,
      .br bop.BEQ true, 15, 12, 0x470#13, 0#21, 0#12⟩ ;;
  [(0x80004c60#64, 0x0186b783#32),
   (0x80004c64#64, 0x0028889b#32)]
  terminator ⟨0x80004c68#64, 0xc8f682e3#32, 0xe3#8, 0x82#8, 0xf6#8, 0xc8#8,
      .br bop.BEQ true, 13, 15, 0x1c84#13, 0#21, 0#12⟩ ;;
  [(0x800048ec#64, 0x02083783#32),
   (0x800048f0#64, 0x00016e97#32),
   (0x800048f4#64, 0x430e8e93#32)]
  terminator ⟨0x800048f8#64, 0x2fd78863#32, 0x63#8, 0x88#8, 0xd7#8, 0x2f#8,
      .br bop.BEQ true, 15, 29, 0x2f0#13, 0#21, 0#12⟩ ;;
  [(0x80004be8#64, 0x00883583#32)]
  terminator ⟨0x80004bec#64, 0xd7dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xd7#8,
      .j, 0, 0, 0#13, 0x1ffd7c#21, 0#12⟩ ;;
  [(0x80004968#64, 0x4028d79b#32),
   (0x8000496c#64, 0x00100513#32),
   (0x80004970#64, 0x00f51533#32)]
  terminator ⟨0x80004974#64, 0x0aa5ec63#32, 0x63#8, 0xec#8, 0xa5#8, 0x0a#8,
      .br bop.BLTU true, 11, 10, 0x0b8#13, 0#21, 0#12⟩
end Vsa.Sim

namespace VsaIris.MallocFast

open Vsa.Sim

/-- The small requests' prologue: the frame, both size tests (not taken). -/
theorem proB_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m)
    {s s0 r n a0 a4 a5 : BitVec 64} (hs : SpGeom s) (hn : n.toNat ≤ 23) :
    ChainFacts m m (proL s s0 r n a0 a4 a5) [] segProB := by
  unfold segProB ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  all_goals seg_norm
  · exact stackStore hs 80 rfl rfl (by decide) (by decide) (by decide)
  · exact stackStore hs 88 rfl rfl (by decide) (by decide) (by decide)
  · rw [ult_false_iff, add_imm n _ 23 (by decide) (by omega)]
    rw [show (0#64 + sign_extend (m := 64) (46#12) : BitVec 64).toNat = 46 by decide]
    omega
  · rw [ult_false_iff, show (0#64 + sign_extend (m := 64) (32#12) : BitVec 64).toNat = 32 by decide]
    omega

/-- The loads of `segBinsB`: both bins' `bk` words, the unsorted bin's `fd`
word, and `binblocks`. -/
abbrev binsLdsB (f : Nat → BitVec 8) : List (List (BitVec 8)) :=
  [wordOf f (Vsa.Sim.DlHeap.binAt 4 + 24), wordOf f (Vsa.Sim.DlHeap.binAt 5 + 24),
   wordOf f (Vsa.Sim.DlHeap.binAt 1 + 16), wordOf f Vsa.Sim.DlHeap.binblocksAddr]

theorem binsB_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m)
    {sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64} {f : Nat → BitVec 8}
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLdsB f) segBinsB := by
  unfold segBinsB ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  all_goals seg_norm
  all_goals (try simp only [binsLdsB, List.tail_cons])
  · refine ldFact rfl (Vsa.Sim.DlHeap.binAt 4 + 24)
      (by unfold eaddrM; seg_norm; decide) (by decide) (by decide)
      (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega))
  · simp only [hb.bk 4 (by decide) (by decide)]; decide
  · refine ldFact rfl (Vsa.Sim.DlHeap.binAt 5 + 24)
      (by unfold eaddrM; seg_norm; decide) (by decide) (by decide)
      (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega))
  · simp only [hb.bk 5 (by decide) (by decide)]; decide
  · refine ldFact rfl (Vsa.Sim.DlHeap.binAt 1 + 16)
      (by unfold eaddrM; seg_norm; decide) (by decide) (by decide)
      (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega))
  · simp only [hb.fd1]; decide
  · refine ldFact rfl Vsa.Sim.DlHeap.binblocksAddr
      (by unfold eaddrM; seg_norm; decide) (by decide) (by decide)
      (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.binblocksAddr Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.binblocksAddr Vsa.Sim.DlHeap.avAddr; omega))
  · simp only [hb.binblocks]; decide

end VsaIris.MallocFast

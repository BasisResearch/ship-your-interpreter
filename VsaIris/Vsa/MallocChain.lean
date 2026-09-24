import VsaIris.Vsa.MallocLarge

/-!
# `_malloc_r` from its entry, on the proved paths

`malloc_paths` chains every `_malloc_r` join proved so far — the prologue and
error return (`malloc_pro`), the small-bin check and take (`j_small`,
`small_take`), the large-bin scan and take (`lscan`), the last-remainder check
and its exact-fit return (`lr_last`), the last remainder's split (`lr_split`),
its re-binning (`rebin`, `rebinL`), the block search's entry, the top split
and `malloc_extend_top` (`bb_top`, `bb_entry`, `extend_top`) — into one statement
from the function's entry `0x800047a8`.

Its hypotheses are exactly the joins still to prove, so the file is the
residual ledger for `IrisHoles.alloc`'s malloc half:

| PC | what runs there |
|---|---|
| `0x80004978` | the block walk over `binblocks` |
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- **From the last-remainder check** (`0x800048ec`) on the proved paths:
the exact-fit or split remainder, its re-binning, the block search's entry,
the top split and `malloc_extend_top`, with the block walk as the one
hypothesis. Both the small path and the large scan end here. -/
theorem from_lr {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb)
    (hnb31 : nb < 2 ^ 31) (hidx : idx < numBins) (hidx1 : 1 < idx)
    (hsf : ScanFrom chunks bins nb idx) (G : LRRegs nb idx R) (h8 : R 8 = reentV)
    (hblocks : ∀ R' Mt brkv' chunks' bins' nb idx bb, MFrame C R' Mt →
      MHeap C Mt brkv' chunks' bins' → bins' 1 = [] → ScanFrom chunks' bins' nb idx →
      NbOK C.n nb → idx < numBins → LRRegs nb idx R' →
      (R' 29).toNat = binAt 1 → R' 8 = reentV → read64 Mt binblocksAddr = some bb →
      2 ^ (idx / 4) ≤ bb → (R' 11).toNat = bb → (R' 10).toNat = 2 ^ (idx / 4) →
      AW C.live C.S C.Q 0x80004978#64 R' Mt) :
    AW C.live C.S C.Q 0x800048ec#64 R Mt := by
  -- after a re-binning: the block search's test
  have hnext : RebinNext C brkv chunks bins nb idx :=
    fun R'' Mt'' bins'' bb'' F'' Hp'' hb1 hsub G'' h29 h8'' hbb h11 =>
      bb_entry O F'' Hp'' G'' h8'' hidx hbb h11 h29
        (fun R' F' G' h8' => top_path O F' Hp'' G' h8' hnb hnb31
          (fun hsm R4 F4 G4 T4 h84 => extend_top O F4 Hp'' G4 T4 h84 hnb hnb31 hsm))
        (fun hle R' F' G' h8' h29' h11' h10' =>
          hblocks R' Mt'' _ _ _ nb _ bb'' F' Hp'' hb1
            (hsf.imp id fun ⟨x, sz, hx, hfr, hle⟩ => ⟨x, sz, hsub idx (by omega) x hx, hfr, hle⟩)
            hnb hidx G' h29' h8' hbb hle h11' h10')
  refine lr_last O F Hp G h8 hnb hnb31 (fun hb1 R3 F3 G3 h29 h83 => ?_)
    (fun v sz hbin hfree hle R3 F3 G3 V3 _ => lr_split O F3 Hp G3 V3 hnb hbin hfree hle)
    (fun v sz hfree hlt R3 Mt3 F3 D3 G3 V3 h83 =>
      rebin O F3 Hp D3 G3 V3 h83 hfree
        (fun hl R' bb F' G' h15 h6 h29 h8' hbb h11 =>
          rebinL O ⟨F', Hp, D3, hfree, hl, rfl, G', h29, h8', h15, h11, hbb⟩ h6 hnext)
        hnext)
  exact bb_top O F3 Hp G3 h83 hidx hnb hnb31
    (fun hsmallTop R4 F4 G4 T4 h84 => extend_top O F4 Hp G4 T4 h84 hnb hnb31 hsmallTop) h29
    (fun bb hbb hle R4 F4 G4 h84 h29' h11 h10 =>
      hblocks R4 Mt _ _ _ nb _ bb F4 Hp hb1 hsf hnb hidx G4 h29' h84 hbb hle h11 h10)

/-- **`_malloc_r` on its proved paths.** From the entry, with the block walk
still open as a hypothesis, a request either returns a block off a small bin,
off its large bin, off the last remainder (whole or split), or off the top
(split in place or after `sbrk` grew it) — or returns NULL because the arena
cannot hold it. A too-small last remainder is re-binned on the way (`rebin`,
`rebinL`). -/
theorem malloc_paths {C : MCtx} (O : MOK C) {R : Nat → BitVec 64}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (E : MEntry C R) (Hp : MHeap C C.Mt0 brkv chunks bins)
    (hblocks : ∀ R' Mt brkv' chunks' bins' nb idx bb, MFrame C R' Mt →
      MHeap C Mt brkv' chunks' bins' → bins' 1 = [] → ScanFrom chunks' bins' nb idx →
      NbOK C.n nb → idx < numBins → LRRegs nb idx R' →
      (R' 29).toNat = binAt 1 → R' 8 = reentV → read64 Mt binblocksAddr = some bb →
      2 ^ (idx / 4) ≤ bb → (R' 11).toNat = bb → (R' 10).toNat = 2 ^ (idx / 4) →
      AW C.live C.S C.Q 0x80004978#64 R' Mt) :
    AW C.live C.S C.Q 0x800047a8#64 R C.Mt0 := by
  refine malloc_pro O E Hp (fun R1 Mt1 nb F1 Hp1 G1 hnb hs503 h81 => ?_)
    (fun R1 Mt1 nb F1 Hp1 hnb h503 hnb31 h14 h81 => lscan O F1 Hp1 hnb h503 hnb31 h14 h81
      fun R' idx hidx hidx1 hsf F' G' h8' => from_lr O F' Hp1 hnb hnb31 hidx hidx1 hsf G' h8' hblocks)
  have hnb31 : nb < 2 ^ 31 := by omega
  refine j_small O F1 Hp1 G1 hnb hs503
    (fun pre v hbin R2 h15 h13 h2 h8 h9 h18 h19 =>
      small_take O (F1.of_regs h2 h9 h18 h19) Hp1 hnb hs503 hbin h15 h13)
    (fun R2 G2 h2 h8 h9 h18 h19 => ?_)
  have hidx : nb / 8 + 2 < numBins := by
    have := hnb.al; have := hnb.lo; unfold numBins; omega
  have hsf : ScanFrom chunks bins nb (nb / 8 + 2) := .inl (by
    unfold binIndex; rw [if_pos (by omega)]; omega)
  exact from_lr O (F1.of_regs h2 h9 h18 h19) Hp1 hnb hnb31 hidx (by omega) hsf G2 (h8.trans h81)
    hblocks

end VsaIris.VsaHeap

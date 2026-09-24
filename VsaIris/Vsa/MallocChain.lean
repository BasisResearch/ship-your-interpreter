import VsaIris.Vsa.MallocRebinL

/-!
# `_malloc_r` from its entry, on the proved paths

`malloc_paths` chains every `_malloc_r` join proved so far — the prologue and
error return (`malloc_pro`), the small-bin check and take (`j_small`,
`small_take`), the last-remainder check and its exact-fit return (`lr_last`),
the last remainder's split (`lr_split`), its re-binning (`rebin`, `rebinL`), the
block search's entry, the top split and `malloc_extend_top` (`bb_top`,
`bb_entry`, `extend_top`) — into one statement
from the function's entry `0x800047a8`.

Its hypotheses are exactly the joins still to prove, so the file is the
residual ledger for `IrisHoles.alloc`'s malloc half:

| PC | what runs there |
|---|---|
| `0x80004884` | the large-bin index and scan |
| `0x80004978` | the block walk over `binblocks` |
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- **`_malloc_r` on its proved paths.** From the entry, with the two joins
still open as hypotheses, a request either returns a block off a small bin,
off the last remainder (whole or split), or off the top (split in place or after
`sbrk` grew it) — or returns NULL because the arena cannot hold it. A
too-small last remainder is re-binned on the way (`rebin`, `rebinL`). -/
theorem malloc_paths {C : MCtx} (O : MOK C) {R : Nat → BitVec 64}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (E : MEntry C R) (Hp : MHeap C C.Mt0 brkv chunks bins)
    (hlarge : ∀ R' Mt nb, MFrame C R' Mt → MHeap C Mt brkv chunks bins → NbOK C.n nb →
      503 < nb → nb < 2 ^ 31 → (R' 14).toNat = nb → R' 8 = reentV →
      AW C.live C.S C.Q 0x80004884#64 R' Mt)
    (hblocks : ∀ R' Mt brkv' chunks' bins' nb idx bb, MFrame C R' Mt →
      MHeap C Mt brkv' chunks' bins' → NbOK C.n nb → idx < numBins → LRRegs nb idx R' →
      (R' 29).toNat = binAt 1 → R' 8 = reentV → read64 Mt binblocksAddr = some bb →
      2 ^ (idx / 4) ≤ bb → (R' 11).toNat = bb → (R' 10).toNat = 2 ^ (idx / 4) →
      AW C.live C.S C.Q 0x80004978#64 R' Mt) :
    AW C.live C.S C.Q 0x800047a8#64 R C.Mt0 := by
  refine malloc_pro O E Hp (fun R1 Mt1 nb F1 Hp1 G1 hnb hs503 h81 => ?_)
    (fun R1 Mt1 nb F1 Hp1 hnb h503 hnb31 h14 h81 => hlarge R1 Mt1 nb F1 Hp1 hnb h503 hnb31 h14 h81)
  have hnb31 : nb < 2 ^ 31 := by omega
  refine j_small O F1 Hp1 G1 hnb hs503
    (fun pre v hbin R2 h15 h13 h2 h8 h9 h18 h19 =>
      small_take O (F1.of_regs h2 h9 h18 h19) Hp1 hnb hs503 hbin h15 h13)
    (fun R2 G2 h2 h8 h9 h18 h19 => ?_)
  have F2 : MFrame C R2 Mt1 := F1.of_regs h2 h9 h18 h19
  have h82 : R2 8 = reentV := h8.trans h81
  have hidx : nb / 8 + 2 < numBins := by
    have := hnb.al; have := hnb.lo; unfold numBins; omega
  -- after a re-binning: the block search's test
  have hnext : RebinNext C brkv chunks nb (nb / 8 + 2) :=
    fun R'' Mt'' bins'' bb'' F'' Hp'' G'' h29 h8'' hbb h11 =>
      bb_entry O F'' Hp'' G'' h8'' hidx hbb h11 h29
        (fun R' F' G' h8' => top_path O F' Hp'' G' h8' hnb hnb31
          (fun hsm R4 F4 G4 T4 h84 => extend_top O F4 Hp'' G4 T4 h84 hnb hnb31 hsm))
        (fun hle R' F' G' h8' h29' h11' h10' =>
          hblocks R' Mt'' _ _ _ nb _ bb'' F' Hp'' hnb hidx G' h29' h8' hbb hle h11' h10')
  refine lr_last O F2 Hp1 G2 h82 hnb hnb31 (fun _ R3 F3 G3 h29 h83 => ?_)
    (fun v sz hbin hfree hle R3 F3 G3 V3 _ => lr_split O F3 Hp1 G3 V3 hnb hbin hfree hle)
    (fun v sz hfree hlt R3 Mt3 F3 D3 G3 V3 h83 =>
      rebin O F3 Hp1 D3 G3 V3 h83 hfree
        (fun hl R' bb F' G' h15 h6 h29 h8' hbb h11 =>
          rebinL O ⟨F', Hp1, D3, hfree, hl, rfl, G', h29, h8', h15, h11, hbb⟩ h6 hnext)
        hnext)
  exact bb_top O F3 Hp1 G3 h83 hidx hnb hnb31
    (fun hsmallTop R4 F4 G4 T4 h84 => extend_top O F4 Hp1 G4 T4 h84 hnb hnb31 hsmallTop) h29
    (fun bb hbb hle R4 F4 G4 h84 h29' h11 h10 =>
      hblocks R4 Mt1 _ _ _ nb _ bb F4 Hp1 hnb hidx G4 h29' h84 hbb hle h11 h10)

end VsaIris.VsaHeap

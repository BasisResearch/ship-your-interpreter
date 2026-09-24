import VsaIris.Vsa.MallocExtend

/-!
# `_malloc_r` from its entry, on the proved paths

`malloc_paths` chains every `_malloc_r` join proved so far — the prologue and
error return (`malloc_pro`), the small-bin check and take (`j_small`,
`small_take`), the last-remainder check and its exact-fit return (`lr_last`),
the block search's entry, the top split and `malloc_extend_top` (`bb_top`,
`extend_top`) — into one statement
from the function's entry `0x800047a8`.

Its hypotheses are exactly the joins still to prove, so the file is the
residual ledger for `IrisHoles.alloc`'s malloc half:

| PC | what runs there |
|---|---|
| `0x80004884` | the large-bin index and scan |
| `0x80004da0` | splitting the last remainder |
| `0x8000491c` | putting a too-small remainder back on its own bin |
| `0x80004978` | the block walk over `binblocks` |
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- **`_malloc_r` on its proved paths.** From the entry, with the four joins
still open as hypotheses, a request either returns a block off a small bin,
off the exact-fit last remainder, or off the top (split in place or after
`sbrk` grew it) — or returns NULL because the arena cannot hold it. -/
theorem malloc_paths {C : MCtx} (O : MOK C) {R : Nat → BitVec 64}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (E : MEntry C R) (Hp : MHeap C C.Mt0 brkv chunks bins)
    (hlarge : ∀ R' Mt nb, MFrame C R' Mt → MHeap C Mt brkv chunks bins → NbOK C.n nb →
      503 < nb → nb < 2 ^ 31 → (R' 14).toNat = nb → R' 8 = reentV →
      AW C.live C.S C.Q 0x80004884#64 R' Mt)
    (hsplit : ∀ R' Mt nb idx v sz, MFrame C R' Mt → MHeap C Mt brkv chunks bins →
      LRRegs nb idx R' → LRVictim nb sz v R' → R' 8 = reentV → bins 1 = [v] →
      FreeAt chunks v sz → nb + 32 ≤ sz → AW C.live C.S C.Q 0x80004da0#64 R' Mt)
    (hrebin : ∀ R' Mt Mt' nb idx v sz, MFrame C R' Mt' → MHeap C Mt brkv chunks bins →
      MDetach C Mt Mt' bins 1 v → LRRegs nb idx R' → LRVictim nb sz v R' → R' 8 = reentV →
      FreeAt chunks v sz → sz < nb → AW C.live C.S C.Q 0x8000491c#64 R' Mt')
    (hblocks : ∀ R' Mt nb idx bb, MFrame C R' Mt → MHeap C Mt brkv chunks bins →
      LRRegs nb idx R' → R' 8 = reentV → read64 Mt binblocksAddr = some bb →
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
  refine lr_last O F2 Hp1 G2 h82 hnb hnb31 (fun _ R3 F3 G3 h83 => ?_)
    (fun v sz hbin hfree hle R3 F3 G3 V3 h83 => hsplit R3 Mt1 nb _ v sz F3 Hp1 G3 V3 h83
      hbin hfree hle)
    (fun v sz hfree hlt R3 Mt3 F3 D3 G3 V3 h83 =>
      hrebin R3 Mt1 Mt3 nb _ v sz F3 Hp1 D3 G3 V3 h83 hfree hlt)
  exact bb_top O F3 Hp1 G3 h83 hidx hnb hnb31
    (fun hsmallTop R4 F4 G4 T4 h84 => extend_top O F4 Hp1 G4 T4 h84 hnb hnb31 hsmallTop)
    (fun bb hbb hle R4 F4 G4 h84 h11 h10 =>
      hblocks R4 Mt1 nb _ bb F4 Hp1 G4 h84 hbb hle h11 h10)

end VsaIris.VsaHeap

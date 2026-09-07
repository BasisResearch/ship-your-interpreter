import Vsa.Sim.rows.FnSflushRFold

/-! # Concrete `__sflush_r` callback-return suffix -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

def sflushEd0cBlock : BBlock :=
  { body := [(mkLine 0x8000ed0c#64 0x40a484bb#32)]
    term := some ⟨0x8000ed10#64, 0xfca04ee3#32,
      0xe3#8, 0x4e#8, 0xa0#8, 0xfc#8,
      .br bop.BLT true, 0, 10, 0x1fdc#13, 0#21, 0#12⟩ }

theorem sflushEd0cSeg_eq : sflush_rXed0cTSeg = [sflushEd0cBlock] := rfl

theorem sflushEd0c_prog_facts (mc m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ProgFactsM mc m (sflushConsoleSuffixL sp) lds sflushEd0cBlock.body := by
  change BytePinsM mc (mkLine 0x8000ed0c#64 0x40a484bb#32) ∧
    DecodeFactM (mkLine 0x8000ed0c#64 0x40a484bb#32) ∧ True ∧ True
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ed0c hcode,
    Vsa.Sim.DecodeTable.decode_40a484bb, trivial, trivial⟩

theorem sflushEd0c_term_pins (mc : Mem)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    TermPins mc sflushEd0cBlock.term := by
  change BytePinsT mc ⟨0x8000ed10#64, 0xfca04ee3#32,
      0xe3#8, 0x4e#8, 0xa0#8, 0xfc#8,
      .br bop.BLT true, 0, 10, 0x1fdc#13, 0#21, 0#12⟩ ∧
    DecodeFactT ⟨0x8000ed10#64, 0xfca04ee3#32,
      0xe3#8, 0x4e#8, 0xa0#8, 0xfc#8,
      .br bop.BLT true, 0, 10, 0x1fdc#13, 0#21, 0#12⟩
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ed10 hcode,
    Vsa.Sim.DecodeTable.decode_fca04ee3⟩

theorem sflushEd0c_term_facts (sp : BitVec 64)
    (lds : List (List (BitVec 8))) :
    TermFactsO (runGM sflushEd0cBlock.body (sflushConsoleSuffixL sp) lds)
      sflushEd0cBlock.term := by
  have hrun : runGM [(mkLine 0x8000ed0c#64 0x40a484bb#32)]
      (sflushConsoleSuffixL sp) lds = sflushSuffixL1 sp := by
    change runChain sflush_rXed0cTSeg (sflushConsoleSuffixL sp) lds = _
    exact sflushEd0c_run sp lds
  change guardB bop.BLT
    (srcVal 0 (runGM [(mkLine 0x8000ed0c#64 0x40a484bb#32)]
      (sflushConsoleSuffixL sp) lds))
    (srcVal 10 (runGM [(mkLine 0x8000ed0c#64 0x40a484bb#32)]
      (sflushConsoleSuffixL sp) lds)) = true
  rw [hrun]
  rfl

theorem sflushEd0c_block_facts (mc m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    BBlockFacts mc m (sflushConsoleSuffixL sp) lds sflushEd0cBlock :=
  ⟨sflushEd0c_prog_facts mc m sp lds hcode,
   sflushEd0c_term_pins mc hcode, sflushEd0c_term_facts sp lds⟩

theorem sflushEd0c_chain_alias (mc m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ChainFacts mc m (sflushConsoleSuffixL sp) lds [sflushEd0cBlock] :=
  ⟨sflushEd0c_block_facts mc m sp lds hcode, trivial⟩

theorem sflushEd0c_facts (mc m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ChainFacts mc m (sflushConsoleSuffixL sp) lds sflush_rXed0cTSeg := by
  rw [sflushEd0cSeg_eq]
  exact sflushEd0c_chain_alias mc m sp lds hcode

theorem sflushEd0c_regs_boundary (sp : BitVec 64)
    (lds : List (List (BitVec 8))) :
    runChain sflush_rXed0cTSeg (sflushConsoleSuffixL sp) lds =
      sflushSuffixL1 sp :=
  sflushEd0c_run sp lds

theorem sflushEd0c_loads_boundary (lds : List (List (BitVec 8))) :
    sflushLoadsChain sflush_rXed0cTSeg lds = lds := by rfl

theorem sflushEd0c_mem_boundary (m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8))) :
    memChain sflush_rXed0cTSeg m (sflushConsoleSuffixL sp) lds = m := by rfl

def sflushEcecBlock : BBlock :=
  { body := [(mkLine 0x8000ecec#64 0x00a90933#32)]
    term := some ⟨0x8000ecf0#64, 0x04905e63#32,
      0x63#8, 0x5e#8, 0x90#8, 0x04#8,
      .br bop.BGE true, 0, 9, 0x005c#13, 0#21, 0#12⟩ }

theorem sflushEcecSeg_eq : sflush_rXececTSeg = [sflushEcecBlock] := rfl

theorem sflushEcec_step (sp : BitVec 64) :
    stepGM (mkLine 0x8000ecec#64 0x00a90933#32)
      (sflushSuffixL1 sp) [] = sflushSuffixL2 sp := by rfl

theorem sflushEcec_run (sp : BitVec 64) (lds : List (List (BitVec 8))) :
    runGM sflushEcecBlock.body (sflushSuffixL1 sp) lds =
      sflushSuffixL2 sp := by
  change runGM [(mkLine 0x8000ecec#64 0x00a90933#32)]
    (sflushSuffixL1 sp) lds = _
  rw [show runGM _ _ _ = runGM []
    (stepGM (mkLine 0x8000ecec#64 0x00a90933#32) (sflushSuffixL1 sp) []) lds
    by rfl]
  exact sflushEcec_step sp

theorem sflushEcec_prog_facts (mc m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ProgFactsM mc m (sflushSuffixL1 sp) lds sflushEcecBlock.body := by
  change BytePinsM mc (mkLine 0x8000ecec#64 0x00a90933#32) ∧
    DecodeFactM (mkLine 0x8000ecec#64 0x00a90933#32) ∧ True ∧ True
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ecec hcode,
    Vsa.Sim.DecodeTable.decode_00a90933, trivial, trivial⟩

theorem sflushEcec_term_pins (mc : Mem)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    TermPins mc sflushEcecBlock.term := by
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ecf0 hcode,
    Vsa.Sim.DecodeTable.decode_04905e63⟩

theorem sflushEcec_term_facts (sp : BitVec 64)
    (lds : List (List (BitVec 8))) :
    TermFactsO (runGM sflushEcecBlock.body (sflushSuffixL1 sp) lds)
      sflushEcecBlock.term := by
  rw [sflushEcec_run sp lds]
  rfl

theorem sflushEcec_block_facts (mc m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    BBlockFacts mc m (sflushSuffixL1 sp) lds sflushEcecBlock :=
  ⟨sflushEcec_prog_facts mc m sp lds hcode,
   sflushEcec_term_pins mc hcode, sflushEcec_term_facts sp lds⟩

theorem sflushEcec_facts (mc m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ChainFacts mc m (sflushSuffixL1 sp) lds sflush_rXececTSeg := by
  rw [sflushEcecSeg_eq]
  exact ⟨sflushEcec_block_facts mc m sp lds hcode, trivial⟩

theorem sflushEcec_regs_boundary (sp : BitVec 64)
    (lds : List (List (BitVec 8))) :
    runChain sflush_rXececTSeg (sflushSuffixL1 sp) lds =
      sflushSuffixL2 sp := by
  change runGM sflushEcecBlock.body (sflushSuffixL1 sp) lds = _
  exact sflushEcec_run sp lds

theorem sflushEcec_loads_boundary (lds : List (List (BitVec 8))) :
    sflushLoadsChain sflush_rXececTSeg lds = lds := by rfl

theorem sflushEcec_mem_boundary (m : Mem) (sp : BitVec 64)
    (lds : List (List (BitVec 8))) :
    memChain sflush_rXececTSeg m (sflushSuffixL1 sp) lds = m := by rfl

def sflushSuffixL3 (sp s1 : BitVec 64) : GRegs :=
  [(9, s1), (18, (BitVec.ofNat 64 consoleBuf : BitVec 64) + 1#64),
   (10, 1#64), (2, sflushSpE sp)]

def sflushEd4cBlock : BBlock :=
  { body := [(mkLine 0x8000ed4c#64 0x01813483#32)]
    term := none }

theorem sflushEd4cSeg_eq : sflush_rXed4cSeg = [sflushEd4cBlock] := rfl

theorem sflushEd4c_step (sp s1 : BitVec 64) :
    stepGM (mkLine 0x8000ed4c#64 0x01813483#32)
      (sflushSuffixL2 sp) (flushBytes8 s1) = sflushSuffixL3 sp s1 := by
  change (9, bytesVal MKind.ld (flushBytes8 s1)) ::
    eraseG 9 (sflushSuffixL2 sp) = sflushSuffixL3 sp s1
  rw [flushBytes8_val]
  rfl

theorem sflushEd4c_run (sp s1 : BitVec 64)
    (rest : List (List (BitVec 8))) :
    runGM sflushEd4cBlock.body (sflushSuffixL2 sp)
      (flushBytes8 s1 :: rest) = sflushSuffixL3 sp s1 := by
  change runGM [(mkLine 0x8000ed4c#64 0x01813483#32)]
    (sflushSuffixL2 sp) (flushBytes8 s1 :: rest) = _
  rw [show runGM _ _ _ = runGM []
    (stepGM (mkLine 0x8000ed4c#64 0x01813483#32)
      (sflushSuffixL2 sp) (flushBytes8 s1)) rest by rfl]
  exact sflushEd4c_step sp s1

theorem sflushEd4c_mem_facts (m : Mem) (sp s1 : BitVec 64)
    (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat
      (flushBytes8 s1)) :
    MemFacts m (sflushSuffixL2 sp) (flushBytes8 s1)
      (mkLine 0x8000ed4c#64 0x01813483#32) := by
  have ha : (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat =
      sp.toNat - 24 := by
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat sp hs 24 (by decide) (by decide)]
    have := hs.htif
    omega
  unfold MemFacts
  change (0x80000000 ≤
      (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat ∧
    (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤
      0x100000000 ∧
    ((sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤
        tohostAddr ∨
      tohostAddr + 8 ≤
        (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat)) ∧ _
  refine ⟨?_, hp⟩
  rw [ha]
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hs.htif
  have := hs.hi
  exact ⟨by omega, by omega, by right; omega⟩

theorem sflushEd4c_prog_facts (mc m : Mem) (sp s1 : BitVec 64)
    (rest : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat
      (flushBytes8 s1)) :
    ProgFactsM mc m (sflushSuffixL2 sp) (flushBytes8 s1 :: rest)
      sflushEd4cBlock.body := by
  change BytePinsM mc (mkLine 0x8000ed4c#64 0x01813483#32) ∧
    DecodeFactM (mkLine 0x8000ed4c#64 0x01813483#32) ∧
    MemFacts m (sflushSuffixL2 sp) (flushBytes8 s1)
      (mkLine 0x8000ed4c#64 0x01813483#32) ∧ True
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ed4c hcode,
    Vsa.Sim.DecodeTable.decode_01813483,
    sflushEd4c_mem_facts m sp s1 hs hp, trivial⟩

theorem sflushEd4c_facts (mc m : Mem) (sp s1 : BitVec 64)
    (rest : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat
      (flushBytes8 s1)) :
    ChainFacts mc m (sflushSuffixL2 sp) (flushBytes8 s1 :: rest)
      sflush_rXed4cSeg := by
  rw [sflushEd4cSeg_eq]
  exact ⟨⟨sflushEd4c_prog_facts mc m sp s1 rest hcode hs hp,
    trivial, trivial⟩, trivial⟩

theorem sflushEd4c_regs_boundary (sp s1 : BitVec 64)
    (rest : List (List (BitVec 8))) :
    runChain sflush_rXed4cSeg (sflushSuffixL2 sp)
      (flushBytes8 s1 :: rest) = sflushSuffixL3 sp s1 := by
  change runGM sflushEd4cBlock.body (sflushSuffixL2 sp)
    (flushBytes8 s1 :: rest) = _
  exact sflushEd4c_run sp s1 rest

theorem sflushEd4c_loads_boundary (s1 : BitVec 64)
    (rest : List (List (BitVec 8))) :
    sflushLoadsChain sflush_rXed4cSeg (flushBytes8 s1 :: rest) = rest := by rfl

theorem sflushEd4c_mem_boundary (m : Mem) (sp s1 : BitVec 64)
    (rest : List (List (BitVec 8))) :
    memChain sflush_rXed4cSeg m (sflushSuffixL2 sp)
      (flushBytes8 s1 :: rest) = m := by rfl

def sflushSuffixL4 (sp s1 s2 : BitVec 64) : GRegs :=
  [(18, s2), (9, s1), (10, 1#64), (2, sflushSpE sp)]

def sflushEd50Block : BBlock :=
  { body := [(mkLine 0x8000ed50#64 0x01013903#32)]
    term := some ⟨0x8000ed54#64, 0xf49ff06f#32,
      0x6f#8, 0xf0#8, 0x9f#8, 0xf4#8,
      .j, 0, 0, 0#13, 0x1fff48#21, 0#12⟩ }

theorem sflushEd50Seg_eq : sflush_rXed50Seg = [sflushEd50Block] := rfl

theorem sflushEd50_step (sp s1 s2 : BitVec 64) :
    stepGM (mkLine 0x8000ed50#64 0x01013903#32)
      (sflushSuffixL3 sp s1) (flushBytes8 s2) = sflushSuffixL4 sp s1 s2 := by
  change (18, bytesVal MKind.ld (flushBytes8 s2)) ::
    eraseG 18 (sflushSuffixL3 sp s1) = sflushSuffixL4 sp s1 s2
  rw [flushBytes8_val]
  rfl

theorem sflushEd50_run (sp s1 s2 : BitVec 64)
    (rest : List (List (BitVec 8))) :
    runGM sflushEd50Block.body (sflushSuffixL3 sp s1)
      (flushBytes8 s2 :: rest) = sflushSuffixL4 sp s1 s2 := by
  change runGM [(mkLine 0x8000ed50#64 0x01013903#32)]
    (sflushSuffixL3 sp s1) (flushBytes8 s2 :: rest) = _
  rw [show runGM _ _ _ = runGM []
    (stepGM (mkLine 0x8000ed50#64 0x01013903#32)
      (sflushSuffixL3 sp s1) (flushBytes8 s2)) rest by rfl]
  exact sflushEd50_step sp s1 s2

theorem sflushEd50_mem_facts (m : Mem) (sp s1 s2 : BitVec 64)
    (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat
      (flushBytes8 s2)) :
    MemFacts m (sflushSuffixL3 sp s1) (flushBytes8 s2)
      (mkLine 0x8000ed50#64 0x01013903#32) := by
  have ha : (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat =
      sp.toNat - 32 := by
    rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      sflush_slot_toNat sp hs 16 (by decide) (by decide)]
    have := hs.htif
    omega
  unfold MemFacts
  change (0x80000000 ≤
      (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat ∧
    (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤
      0x100000000 ∧
    ((sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤
        tohostAddr ∨
      tohostAddr + 8 ≤
        (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat)) ∧ _
  refine ⟨?_, hp⟩
  rw [ha]
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hs.htif
  have := hs.hi
  exact ⟨by omega, by omega, by right; omega⟩

theorem sflushEd50_prog_facts (mc m : Mem) (sp s1 s2 : BitVec 64)
    (rest : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat
      (flushBytes8 s2)) :
    ProgFactsM mc m (sflushSuffixL3 sp s1) (flushBytes8 s2 :: rest)
      sflushEd50Block.body := by
  change BytePinsM mc (mkLine 0x8000ed50#64 0x01013903#32) ∧
    DecodeFactM (mkLine 0x8000ed50#64 0x01013903#32) ∧
    MemFacts m (sflushSuffixL3 sp s1) (flushBytes8 s2)
      (mkLine 0x8000ed50#64 0x01013903#32) ∧ True
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ed50 hcode,
    Vsa.Sim.DecodeTable.decode_01013903,
    sflushEd50_mem_facts m sp s1 s2 hs hp, trivial⟩

theorem sflushEd50_term_pins (mc : Mem)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    TermPins mc sflushEd50Block.term := by
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ed54 hcode,
    Vsa.Sim.DecodeTable.decode_f49ff06f⟩

theorem sflushEd50_facts (mc m : Mem) (sp s1 s2 : BitVec 64)
    (rest : List (List (BitVec 8)))
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat
      (flushBytes8 s2)) :
    ChainFacts mc m (sflushSuffixL3 sp s1) (flushBytes8 s2 :: rest)
      sflush_rXed50Seg := by
  rw [sflushEd50Seg_eq]
  exact ⟨⟨sflushEd50_prog_facts mc m sp s1 s2 rest hcode hs hp,
    sflushEd50_term_pins mc hcode, trivial⟩, trivial⟩

theorem sflushEd50_regs_boundary (sp s1 s2 : BitVec 64)
    (rest : List (List (BitVec 8))) :
    runChain sflush_rXed50Seg (sflushSuffixL3 sp s1)
      (flushBytes8 s2 :: rest) = sflushSuffixL4 sp s1 s2 := by
  change runGM sflushEd50Block.body (sflushSuffixL3 sp s1)
    (flushBytes8 s2 :: rest) = _
  exact sflushEd50_run sp s1 s2 rest

theorem sflushEd50_loads_boundary (s2 : BitVec 64)
    (rest : List (List (BitVec 8))) :
    sflushLoadsChain sflush_rXed50Seg (flushBytes8 s2 :: rest) = rest := by rfl

theorem sflushEd50_mem_boundary (m : Mem) (sp s1 s2 : BitVec 64)
    (rest : List (List (BitVec 8))) :
    memChain sflush_rXed50Seg m (sflushSuffixL3 sp s1)
      (flushBytes8 s2 :: rest) = m := by rfl

def sflushSuffixL4a (sp ra s1 s2 : BitVec 64) : GRegs :=
  [(1, ra), (18, s2), (9, s1), (10, 1#64), (2, sflushSpE sp)]

def sflushSuffixL4b (sp ra s0 s1 s2 : BitVec 64) : GRegs :=
  [(8, s0), (1, ra), (18, s2), (9, s1), (10, 1#64), (2, sflushSpE sp)]

def sflushSuffixL4c (sp ra s0 s1 s2 s3 : BitVec 64) : GRegs :=
  [(19, s3), (8, s0), (1, ra), (18, s2), (9, s1), (10, 1#64),
   (2, sflushSpE sp)]

def sflushSuffixL4d (sp ra s0 s1 s2 s3 : BitVec 64) : GRegs :=
  [(10, 0#64), (19, s3), (8, s0), (1, ra), (18, s2), (9, s1),
   (2, sflushSpE sp)]

def sflushSuffixL5 (sp ra s0 s1 s2 s3 : BitVec 64) : GRegs :=
  [(2, sflushSpE sp + sign_extend (m := 64) (0x030#12)),
   (10, 0#64), (19, s3), (8, s0), (1, ra), (18, s2), (9, s1)]

def sflushEc9cBlock : BBlock :=
  { body := [(mkLine 0x8000ec9c#64 0x02813083#32),
      (mkLine 0x8000eca0#64 0x02013403#32),
      (mkLine 0x8000eca4#64 0x00813983#32),
      (mkLine 0x8000eca8#64 0x00000513#32),
      (mkLine 0x8000ecac#64 0x03010113#32)]
    term := some ⟨0x8000ecb0#64, 0x00008067#32,
      0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩ }

theorem sflushEc9cSeg_eq : sflush_rXec9cSeg = [sflushEc9cBlock] := rfl

theorem sflushEc9c_step_ra (sp ra s1 s2 : BitVec 64) :
    stepGM (mkLine 0x8000ec9c#64 0x02813083#32)
      (sflushSuffixL4 sp s1 s2) (flushBytes8 ra) =
      sflushSuffixL4a sp ra s1 s2 := by
  change (1, bytesVal MKind.ld (flushBytes8 ra)) ::
    eraseG 1 (sflushSuffixL4 sp s1 s2) = _
  rw [flushBytes8_val]
  rfl

theorem sflushEc9c_step_s0 (sp ra s0 s1 s2 : BitVec 64) :
    stepGM (mkLine 0x8000eca0#64 0x02013403#32)
      (sflushSuffixL4a sp ra s1 s2) (flushBytes8 s0) =
      sflushSuffixL4b sp ra s0 s1 s2 := by
  change (8, bytesVal MKind.ld (flushBytes8 s0)) ::
    eraseG 8 (sflushSuffixL4a sp ra s1 s2) = _
  rw [flushBytes8_val]
  rfl

theorem sflushEc9c_step_s3 (sp ra s0 s1 s2 s3 : BitVec 64) :
    stepGM (mkLine 0x8000eca4#64 0x00813983#32)
      (sflushSuffixL4b sp ra s0 s1 s2) (flushBytes8 s3) =
      sflushSuffixL4c sp ra s0 s1 s2 s3 := by
  change (19, bytesVal MKind.ld (flushBytes8 s3)) ::
    eraseG 19 (sflushSuffixL4b sp ra s0 s1 s2) = _
  rw [flushBytes8_val]
  rfl

theorem sflushEc9c_step_li (sp ra s0 s1 s2 s3 : BitVec 64) :
    stepGM (mkLine 0x8000eca8#64 0x00000513#32)
      (sflushSuffixL4c sp ra s0 s1 s2 s3) [] =
      sflushSuffixL4d sp ra s0 s1 s2 s3 := by rfl

theorem sflushEc9c_step_sp (sp ra s0 s1 s2 s3 : BitVec 64) :
    stepGM (mkLine 0x8000ecac#64 0x03010113#32)
      (sflushSuffixL4d sp ra s0 s1 s2 s3) [] =
      sflushSuffixL5 sp ra s0 s1 s2 s3 := by rfl

theorem sflushEc9c_run_ra (sp ra s0 s1 s2 s3 : BitVec 64) :
    runGM sflushEc9cBlock.body (sflushSuffixL4 sp s1 s2)
      [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3] =
    runGM [(mkLine 0x8000eca0#64 0x02013403#32),
      (mkLine 0x8000eca4#64 0x00813983#32),
      (mkLine 0x8000eca8#64 0x00000513#32),
      (mkLine 0x8000ecac#64 0x03010113#32)]
      (sflushSuffixL4a sp ra s1 s2) [flushBytes8 s0, flushBytes8 s3] := by
  rw [show runGM sflushEc9cBlock.body _ _ = runGM _
    (stepGM (mkLine 0x8000ec9c#64 0x02813083#32)
      (sflushSuffixL4 sp s1 s2) (flushBytes8 ra))
    [flushBytes8 s0, flushBytes8 s3] by rfl,
    sflushEc9c_step_ra]

theorem sflushEc9c_run_s0 (sp ra s0 s1 s2 s3 : BitVec 64) :
    runGM [(mkLine 0x8000eca0#64 0x02013403#32),
      (mkLine 0x8000eca4#64 0x00813983#32),
      (mkLine 0x8000eca8#64 0x00000513#32),
      (mkLine 0x8000ecac#64 0x03010113#32)]
      (sflushSuffixL4a sp ra s1 s2) [flushBytes8 s0, flushBytes8 s3] =
    runGM [(mkLine 0x8000eca4#64 0x00813983#32),
      (mkLine 0x8000eca8#64 0x00000513#32),
      (mkLine 0x8000ecac#64 0x03010113#32)]
      (sflushSuffixL4b sp ra s0 s1 s2) [flushBytes8 s3] := by
  rw [show runGM _ _ _ = runGM _
    (stepGM (mkLine 0x8000eca0#64 0x02013403#32)
      (sflushSuffixL4a sp ra s1 s2) (flushBytes8 s0))
    [flushBytes8 s3] by rfl, sflushEc9c_step_s0]

theorem sflushEc9c_run_s3 (sp ra s0 s1 s2 s3 : BitVec 64) :
    runGM [(mkLine 0x8000eca4#64 0x00813983#32),
      (mkLine 0x8000eca8#64 0x00000513#32),
      (mkLine 0x8000ecac#64 0x03010113#32)]
      (sflushSuffixL4b sp ra s0 s1 s2) [flushBytes8 s3] =
    runGM [(mkLine 0x8000eca8#64 0x00000513#32),
      (mkLine 0x8000ecac#64 0x03010113#32)]
      (sflushSuffixL4c sp ra s0 s1 s2 s3) [] := by
  rw [show runGM _ _ _ = runGM _
    (stepGM (mkLine 0x8000eca4#64 0x00813983#32)
      (sflushSuffixL4b sp ra s0 s1 s2) (flushBytes8 s3)) [] by rfl,
    sflushEc9c_step_s3]

theorem sflushEc9c_run_tail (sp ra s0 s1 s2 s3 : BitVec 64) :
    runGM [(mkLine 0x8000eca8#64 0x00000513#32),
      (mkLine 0x8000ecac#64 0x03010113#32)]
      (sflushSuffixL4c sp ra s0 s1 s2 s3) [] =
      sflushSuffixL5 sp ra s0 s1 s2 s3 := by
  rw [show runGM _ _ _ = runGM [(mkLine 0x8000ecac#64 0x03010113#32)]
    (stepGM (mkLine 0x8000eca8#64 0x00000513#32)
      (sflushSuffixL4c sp ra s0 s1 s2 s3) []) [] by rfl,
    sflushEc9c_step_li]
  rw [show runGM _ _ _ = runGM []
    (stepGM (mkLine 0x8000ecac#64 0x03010113#32)
      (sflushSuffixL4d sp ra s0 s1 s2 s3) []) [] by rfl,
    sflushEc9c_step_sp]
  rfl

theorem sflushEc9c_run (sp ra s0 s1 s2 s3 : BitVec 64) :
    runGM sflushEc9cBlock.body (sflushSuffixL4 sp s1 s2)
      [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3] =
      sflushSuffixL5 sp ra s0 s1 s2 s3 := by
  rw [sflushEc9c_run_ra, sflushEc9c_run_s0, sflushEc9c_run_s3,
    sflushEc9c_run_tail]

theorem sflush_stack_load_range (sp : BitVec 64) (hs : SflushStackOK sp)
    (off : Nat) (hi : off < 2048) (hoff : off ≤ 40) (halign : off % 8 = 0) :
    0x80000000 ≤ (sflushSpE sp + BitVec.ofNat 64 off).toNat ∧
    (sflushSpE sp + BitVec.ofNat 64 off).toNat + 8 ≤ 0x100000000 ∧
    ((sflushSpE sp + BitVec.ofNat 64 off).toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (sflushSpE sp + BitVec.ofNat 64 off).toNat) := by
  rw [sflush_slot_toNat sp hs off hi (by omega)]
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hs.htif
  have := hs.hi
  exact ⟨by omega, by omega, by right; omega⟩

theorem sflushEc9c_mem_ra (m : Mem) (sp ra s1 s2 : BitVec 64)
    (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat
      (flushBytes8 ra)) :
    MemFacts m (sflushSuffixL4 sp s1 s2) (flushBytes8 ra)
      (mkLine 0x8000ec9c#64 0x02813083#32) := by
  unfold MemFacts
  change (0x80000000 ≤
      (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat ∧
    (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤
      0x100000000 ∧
    ((sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤
        tohostAddr ∨
      tohostAddr + 8 ≤
        (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat)) ∧ _
  rw [show sign_extend (m := 64) (0x028#12) = (40#64) by decide]
  exact ⟨sflush_stack_load_range sp hs 40 (by decide) (by decide) (by decide), hp⟩

theorem sflushEc9c_mem_s0 (m : Mem) (sp ra s0 s1 s2 : BitVec 64)
    (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat
      (flushBytes8 s0)) :
    MemFacts m (sflushSuffixL4a sp ra s1 s2) (flushBytes8 s0)
      (mkLine 0x8000eca0#64 0x02013403#32) := by
  unfold MemFacts
  change (0x80000000 ≤
      (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat ∧
    (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤
      0x100000000 ∧
    ((sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤
        tohostAddr ∨
      tohostAddr + 8 ≤
        (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat)) ∧ _
  rw [show sign_extend (m := 64) (0x020#12) = (32#64) by decide]
  exact ⟨sflush_stack_load_range sp hs 32 (by decide) (by decide) (by decide), hp⟩

theorem sflushEc9c_mem_s3 (m : Mem) (sp ra s0 s1 s2 s3 : BitVec 64)
    (hs : SflushStackOK sp)
    (hp : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat
      (flushBytes8 s3)) :
    MemFacts m (sflushSuffixL4b sp ra s0 s1 s2) (flushBytes8 s3)
      (mkLine 0x8000eca4#64 0x00813983#32) := by
  unfold MemFacts
  change (0x80000000 ≤
      (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat ∧
    (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤
      0x100000000 ∧
    ((sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤
        tohostAddr ∨
      tohostAddr + 8 ≤
        (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat)) ∧ _
  rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide]
  exact ⟨sflush_stack_load_range sp hs 8 (by decide) (by decide) (by decide), hp⟩

theorem sflushEc9c_prog_facts (mc m : Mem)
    (sp ra s0 s1 s2 s3 : BitVec 64)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc)
    (hs : SflushStackOK sp)
    (hra : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat
      (flushBytes8 ra))
    (hs0 : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat
      (flushBytes8 s0))
    (hs3 : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat
      (flushBytes8 s3)) :
    ProgFactsM mc m (sflushSuffixL4 sp s1 s2)
      [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3]
      sflushEc9cBlock.body := by
  change
    BytePinsM mc (mkLine 0x8000ec9c#64 0x02813083#32) ∧
    DecodeFactM (mkLine 0x8000ec9c#64 0x02813083#32) ∧
    MemFacts m (sflushSuffixL4 sp s1 s2) (flushBytes8 ra)
      (mkLine 0x8000ec9c#64 0x02813083#32) ∧
    BytePinsM mc (mkLine 0x8000eca0#64 0x02013403#32) ∧
    DecodeFactM (mkLine 0x8000eca0#64 0x02013403#32) ∧
    MemFacts m (sflushSuffixL4a sp ra s1 s2) (flushBytes8 s0)
      (mkLine 0x8000eca0#64 0x02013403#32) ∧
    BytePinsM mc (mkLine 0x8000eca4#64 0x00813983#32) ∧
    DecodeFactM (mkLine 0x8000eca4#64 0x00813983#32) ∧
    MemFacts m (sflushSuffixL4b sp ra s0 s1 s2) (flushBytes8 s3)
      (mkLine 0x8000eca4#64 0x00813983#32) ∧
    BytePinsM mc (mkLine 0x8000eca8#64 0x00000513#32) ∧
    DecodeFactM (mkLine 0x8000eca8#64 0x00000513#32) ∧ True ∧
    BytePinsM mc (mkLine 0x8000ecac#64 0x03010113#32) ∧
    DecodeFactM (mkLine 0x8000ecac#64 0x03010113#32) ∧ True ∧ True
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ec9c hcode,
    Vsa.Sim.DecodeTable.decode_02813083,
    sflushEc9c_mem_ra m sp ra s1 s2 hs hra,
    Vsa.Sim.Code.__sflush_r_at_8000eca0 hcode,
    Vsa.Sim.DecodeTable.decode_02013403,
    sflushEc9c_mem_s0 m sp ra s0 s1 s2 hs hs0,
    Vsa.Sim.Code.__sflush_r_at_8000eca4 hcode,
    Vsa.Sim.DecodeTable.decode_00813983,
    sflushEc9c_mem_s3 m sp ra s0 s1 s2 s3 hs hs3,
    Vsa.Sim.Code.__sflush_r_at_8000eca8 hcode,
    Vsa.Sim.DecodeTable.decode_00000513, trivial,
    Vsa.Sim.Code.__sflush_r_at_8000ecac hcode,
    Vsa.Sim.DecodeTable.decode_03010113, trivial, trivial⟩

theorem sflushEc9c_term_pins (mc : Mem)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    TermPins mc sflushEc9cBlock.term := by
  exact ⟨Vsa.Sim.Code.__sflush_r_at_8000ecb0 hcode,
    Vsa.Sim.DecodeTable.decode_00008067⟩

theorem sflushEc9c_term_facts (sp ra s0 s1 s2 s3 : BitVec 64)
    (hra : ra.toNat % 4 = 0) :
    TermFactsO
      (runGM sflushEc9cBlock.body (sflushSuffixL4 sp s1 s2)
        [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3])
      sflushEc9cBlock.term := by
  rw [sflushEc9c_run]
  change (BitVec.update
    (srcVal 1 (sflushSuffixL5 sp ra s0 s1 s2 s3) +
      sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
  change (BitVec.update (ra + sign_extend (m := 64) (0x000#12))
    0 0#1).toNat % 4 = 0
  rw [ret_tgt ra hra]
  exact hra

theorem sflushEc9c_block_facts (mc m : Mem)
    (sp ra s0 s1 s2 s3 : BitVec 64)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc)
    (hs : SflushStackOK sp) (hralign : ra.toNat % 4 = 0)
    (hra : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat
      (flushBytes8 ra))
    (hs0 : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat
      (flushBytes8 s0))
    (hs3 : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat
      (flushBytes8 s3)) :
    BBlockFacts mc m (sflushSuffixL4 sp s1 s2)
      [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3]
      sflushEc9cBlock :=
  ⟨sflushEc9c_prog_facts mc m sp ra s0 s1 s2 s3 hcode hs hra hs0 hs3,
   sflushEc9c_term_pins mc hcode,
   sflushEc9c_term_facts sp ra s0 s1 s2 s3 hralign⟩

theorem sflushEc9c_facts (mc m : Mem)
    (sp ra s0 s1 s2 s3 : BitVec 64)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc)
    (hs : SflushStackOK sp) (hralign : ra.toNat % 4 = 0)
    (hra : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat
      (flushBytes8 ra))
    (hs0 : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat
      (flushBytes8 s0))
    (hs3 : LPins8 m
      (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat
      (flushBytes8 s3)) :
    ChainFacts mc m (sflushSuffixL4 sp s1 s2)
      [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3]
      sflush_rXec9cSeg := by
  rw [sflushEc9cSeg_eq]
  exact ⟨sflushEc9c_block_facts mc m sp ra s0 s1 s2 s3 hcode hs
    hralign hra hs0 hs3, trivial⟩

theorem sflushEc9c_regs_boundary (sp ra s0 s1 s2 s3 : BitVec 64) :
    runChain sflush_rXec9cSeg (sflushSuffixL4 sp s1 s2)
      [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3] =
      sflushSuffixL5 sp ra s0 s1 s2 s3 := by
  change runGM sflushEc9cBlock.body (sflushSuffixL4 sp s1 s2)
    [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3] = _
  exact sflushEc9c_run sp ra s0 s1 s2 s3

theorem sflushEc9c_loads_boundary (ra s0 s3 : BitVec 64) :
    sflushLoadsChain sflush_rXec9cSeg
      [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3] = [] := by
  rfl

theorem sflushEc9c_mem_boundary (m : Mem)
    (sp ra s0 s1 s2 s3 : BitVec 64) :
    memChain sflush_rXec9cSeg m (sflushSuffixL4 sp s1 s2)
      [flushBytes8 ra, flushBytes8 s0, flushBytes8 s3] = m := by
  rfl

theorem sflushLoadsChain_append_calc (xs ys : List BBlock)
    (lds : List (List (BitVec 8))) :
    sflushLoadsChain (xs ++ ys) lds =
      sflushLoadsChain ys (sflushLoadsChain xs lds) := by
  induction xs generalizing lds with
  | nil => rfl
  | cons b bs ih => exact ih _

theorem sflushConsoleSuffix_facts_all (g : SflushG) (hg : SflushGOk g) :
    ChainFacts (sflushCallbackM g) (sflushCallbackM g)
      (sflushConsoleSuffixL g.sp) (sflushConsoleSuffixLds g)
      sflushConsoleSuffixSeg := by
  have hcode := sflushCallbackM_code g hg
  have h1 := sflushEd0c_facts (sflushCallbackM g) (sflushCallbackM g)
    g.sp (sflushConsoleSuffixLds g) hcode
  have h2 := sflushEcec_facts (sflushCallbackM g) (sflushCallbackM g)
    g.sp (sflushConsoleSuffixLds g) hcode
  have h3 := sflushEd4c_facts (sflushCallbackM g) (sflushCallbackM g)
    g.sp g.sv.s1
    [flushBytes8 g.sv.s2, flushBytes8 g.ra, flushBytes8 g.s0,
      flushBytes8 g.sv.s3]
    hcode hg.stack (sflushCallback_lpins_s1 g hg)
  have h4 := sflushEd50_facts (sflushCallbackM g) (sflushCallbackM g)
    g.sp g.sv.s1 g.sv.s2
    [flushBytes8 g.ra, flushBytes8 g.s0, flushBytes8 g.sv.s3]
    hcode hg.stack (sflushCallback_lpins_s2 g hg)
  have h5 := sflushEc9c_facts (sflushCallbackM g) (sflushCallbackM g)
    g.sp g.ra g.s0 g.sv.s1 g.sv.s2 g.sv.s3 hcode hg.stack
    hg.ra_align (sflushCallback_lpins_ra g hg)
    (sflushCallback_lpins_s0 g hg) (sflushCallback_lpins_s3 g hg)
  rw [sflushConsoleSuffixSeg, List.append_assoc, List.append_assoc,
    List.append_assoc]
  simp only [sflushConsoleSuffixLds]
  apply chainFacts_append_calc _ _ _ _ _ _ h1
  rw [sflushEd0c_mem_boundary, sflushEd0c_regs_boundary,
    sflushEd0c_loads_boundary]
  apply chainFacts_append_calc _ _ _ _ _ _ h2
  rw [sflushEcec_mem_boundary, sflushEcec_regs_boundary,
    sflushEcec_loads_boundary]
  apply chainFacts_append_calc _ _ _ _ _ _ h3
  rw [sflushEd4c_mem_boundary, sflushEd4c_regs_boundary,
    sflushEd4c_loads_boundary]
  apply chainFacts_append_calc _ _ _ _ _ _ h4
  rw [sflushEd50_mem_boundary, sflushEd50_regs_boundary,
    sflushEd50_loads_boundary]
  exact h5

theorem sflushConsoleSuffix_regs (g : SflushG) :
    runChain sflushConsoleSuffixSeg (sflushConsoleSuffixL g.sp)
      (sflushConsoleSuffixLds g) =
      sflushSuffixL5 g.sp g.ra g.s0 g.sv.s1 g.sv.s2 g.sv.s3 := by
  rw [sflushConsoleSuffixSeg, List.append_assoc, List.append_assoc,
    List.append_assoc]
  simp only [sflushConsoleSuffixLds]
  rw [runChain_append_calc, sflushEd0c_regs_boundary,
    sflushEd0c_loads_boundary]
  rw [runChain_append_calc, sflushEcec_regs_boundary,
    sflushEcec_loads_boundary]
  rw [runChain_append_calc, sflushEd4c_regs_boundary,
    sflushEd4c_loads_boundary]
  rw [runChain_append_calc, sflushEd50_regs_boundary,
    sflushEd50_loads_boundary]
  exact sflushEc9c_regs_boundary g.sp g.ra g.s0 g.sv.s1 g.sv.s2 g.sv.s3

theorem sflushConsoleSuffix_loads (g : SflushG) :
    sflushLoadsChain sflushConsoleSuffixSeg (sflushConsoleSuffixLds g) = [] := by
  rw [sflushConsoleSuffixSeg, List.append_assoc, List.append_assoc,
    List.append_assoc]
  simp only [sflushConsoleSuffixLds]
  rw [sflushLoadsChain_append_calc, sflushEd0c_loads_boundary]
  rw [sflushLoadsChain_append_calc, sflushEcec_loads_boundary]
  rw [sflushLoadsChain_append_calc, sflushEd4c_loads_boundary]
  rw [sflushLoadsChain_append_calc, sflushEd50_loads_boundary,
    sflushEc9c_loads_boundary]

theorem sflushConsoleSuffix_mem (g : SflushG) :
    memChain sflushConsoleSuffixSeg (sflushCallbackM g)
      (sflushConsoleSuffixL g.sp) (sflushConsoleSuffixLds g) =
      sflushCallbackM g := by
  rw [sflushConsoleSuffixSeg, List.append_assoc, List.append_assoc,
    List.append_assoc]
  simp only [sflushConsoleSuffixLds]
  rw [memChain_append_calc, sflushEd0c_mem_boundary,
    sflushEd0c_regs_boundary, sflushEd0c_loads_boundary]
  rw [memChain_append_calc, sflushEcec_mem_boundary,
    sflushEcec_regs_boundary, sflushEcec_loads_boundary]
  rw [memChain_append_calc, sflushEd4c_mem_boundary,
    sflushEd4c_regs_boundary, sflushEd4c_loads_boundary]
  rw [memChain_append_calc, sflushEd50_mem_boundary,
    sflushEd50_regs_boundary, sflushEd50_loads_boundary]
  exact sflushEc9c_mem_boundary (sflushCallbackM g) g.sp g.ra g.s0
    g.sv.s1 g.sv.s2 g.sv.s3

theorem sflush_sp_restore (sp : BitVec 64) :
    sflushSpE sp + sign_extend (m := 64) (0x030#12) = sp := by
  unfold sflushSpE
  rw [show sign_extend (m := 64) (0xfd0#12) = 0xffffffffffffffd0#64 by decide,
    show sign_extend (m := 64) (0x030#12) = 48#64 by decide]
  rw [BitVec.add_assoc]
  exact BitVec.add_zero sp

theorem sflushConsoleSuffix_pc (g : SflushG) (hg : SflushGOk g) :
    evalBlocksPC 0x8000ed0c#64
      (SegEvalState.init (sflushConsoleSuffixL g.sp)
        (sflushConsoleSuffixLds g)) sflushConsoleSuffixSeg = g.ra := by
  change BitVec.update
    (srcVal 1
      (runGM sflushEc9cBlock.body
        (sflushSuffixL4 g.sp g.sv.s1 g.sv.s2)
        [flushBytes8 g.ra, flushBytes8 g.s0, flushBytes8 g.sv.s3]) +
      sign_extend (m := 64) (0x000#12)) 0 0#1 = g.ra
  rw [sflushEc9c_run]
  have hsrc : srcVal 1
      (sflushSuffixL5 g.sp g.ra g.s0 g.sv.s1 g.sv.s2 g.sv.s3) = g.ra := by
    rfl
  rw [hsrc, ret_tgt g.ra hg.ra_align]

def sflushSuffixKeep (g : SflushG) : GRegs :=
  [(3, wrGpVal), (20, g.sv.s4), (21, g.sv.s5), (22, g.sv.s6),
   (23, g.sv.s7), (24, g.sv.s8), (25, g.sv.s9), (26, g.sv.s10),
   (27, g.sv.s11)]

structure SflushFnPost (g : SflushG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sflushCallbackM g
  pc : c.σ.regs.get? Register.PC = some g.ra
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some 0#64
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some g.sp
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 [g.ch]
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

theorem sflushSuffixArm (g : SflushG) (hg : SflushGOk g) :
    Triple (SwFnPost (sflushSWG g)) (SflushFnPost g) := by
  have T := segRowFramed sflushConsoleSuffixSeg
    (sflushConsoleSuffixL g.sp) (sflushConsoleSuffixLds g)
    0x8000ed0c#64 (sflushCallbackM g) (sflushSuffixKeep g)
    (pushBytes g.out0 [g.ch]) (0#4)
    (by
      show ChainOK 0x8000ed0c#64 [9, 10, 18, 2]
        sflushConsoleSuffixSeg
      decide)
    (by
      show FrameOK [3, 20, 21, 22, 23, 24, 25, 26, 27]
        sflushConsoleSuffixSeg
      decide)
  intro c hp
  obtain ⟨ks1, ks2, ks3, ks4, ks5, ks6, ks7, ks8, ks9, ks10, ks11, -⟩ :=
    hp.sregs
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (sflushConsoleSuffixL g.sp) (sflushConsoleSuffixLds g)
      sflushConsoleSuffixSeg := by
    rw [hp.mem]
    exact sflushConsoleSuffix_facts_all g hg
  obtain ⟨c1, hsteps, h1⟩ := T c
    { seg := ⟨hp.good, hp.mem, hp.pc, hp.minstret,
        ⟨ks1, hp.a0, ks2, hp.sp, trivial⟩,
        by show KeysOK [9, 10, 18, 2]; decide,
        hfacts, hp.tick⟩
      keep := ⟨hp.gp, ks4, ks5, ks6, ks7, ks8, ks9, ks10, ks11, trivial⟩
      out := hp.out
      pw := hp.pw
      th := hp.th }
  have hregs : GHolds c1.σ
      (sflushSuffixL5 g.sp g.ra g.s0 g.sv.s1 g.sv.s2 g.sv.s3) := by
    have hr := h1.regs
    rw [evalBlocks_regs] at hr
    change GHolds c1.σ
      (runChain sflushConsoleSuffixSeg (sflushConsoleSuffixL g.sp)
        (sflushConsoleSuffixLds g)) at hr
    rw [sflushConsoleSuffix_regs] at hr
    exact hr
  obtain ⟨kgp, kh4, kh5, kh6, kh7, kh8, kh9, kh10, kh11, -⟩ := h1.keep
  refine ⟨c1, hsteps, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by
        rw [h1.mem, writeLog_evalBlocks_init, sflushConsoleSuffix_mem]
      pc := by rw [h1.pc, sflushConsoleSuffix_pc g hg]
      minstret := h1.minstret
      a0 := gholds_lookup (v := 0#64) _ hregs (by rfl)
      ra := gholds_lookup (v := g.ra) _ hregs (by rfl)
      sp := by
        have hs := gholds_lookup (n := 2)
          (v := sflushSpE g.sp + sign_extend (m := 64) (0x030#12))
          _ hregs (by rfl)
        rwa [sflush_sp_restore] at hs
      gp := kgp
      s0 := gholds_lookup (v := g.s0) _ hregs (by rfl)
      sregs := ⟨gholds_lookup (v := g.sv.s1) _ hregs (by rfl),
        gholds_lookup (v := g.sv.s2) _ hregs (by rfl),
        gholds_lookup (v := g.sv.s3) _ hregs (by rfl),
        kh4, kh5, kh6, kh7, kh8, kh9, kh10, kh11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- Concrete one-byte `__sflush_r` success route, including the indirect
`__swrite` callback and the exact restore/return suffix. -/
theorem sflush_summary (g : SflushG) :
    FnSummary 0x8000eb70#64 (SflushFnPre g) (SflushFnPost g) := by
  refine ⟨?_⟩
  intro c hc
  have hg := hc.2.ok
  exact Triple.seq (sflushPrefixArm g hg)
    (Triple.seq (sflushCallbackArm g hg) (sflushSuffixArm g hg)) c hc

#print axioms sflush_summary

theorem sflushSWG_clr (g : SflushG) :
    swClr (sflushSWG g) = 0x200a#64 := by
  simp only [swClr, swFlags, sflushSWG, swMask, bytesVal]
  decide

theorem sflushSwM2_flag0 (g : SflushG) (hg : SflushGOk g) :
    (swM2 (sflushSWG g))[consoleStdout + 16]? = some 0x0a#8 := by
  have hsw := sflushSWG_ok g hg
  unfold swM2 swTailLog writeLog
  simp only [List.foldl_cons, List.foldl_nil, applyW]
  rw [sw_flAddr (sflushSWG g) hsw, sflushSWG_clr]
  simp only [sflushSWG, BitVec.toNat_ofNat]
  simp only [shData]
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by decide),
    Std.ExtHashMap.getElem?_insert, if_pos (by decide)]
  decide

theorem sflushSwM2_flag1 (g : SflushG) (hg : SflushGOk g) :
    (swM2 (sflushSWG g))[consoleStdout + 17]? = some 0x20#8 := by
  have hsw := sflushSWG_ok g hg
  unfold swM2 swTailLog writeLog
  simp only [List.foldl_cons, List.foldl_nil, applyW]
  rw [sw_flAddr (sflushSWG g) hsw, sflushSWG_clr]
  simp only [sflushSWG, BitVec.toNat_ofNat]
  simp only [shData]
  rw [Std.ExtHashMap.getElem?_insert, if_pos (by decide)]
  decide

theorem consoleFoot_lt_stdout_end (a : Nat) (ha : ConsoleFoot a) :
    a < consoleStdout + 184 := by
  rcases ha with ha | ha | ha | rfl
  · rcases ha with ⟨_, h⟩
    dsimp [consoleImpurePtrAddr, consoleStdout] at *
    omega
  · rcases ha with ⟨_, h⟩
    dsimp [consoleReent, consoleStdout] at *
    omega
  · exact ha.2
  · dsimp [consoleBuf, consoleStdout]
    omega

theorem consoleFoot_errno_disjoint (a : Nat) (ha : ConsoleFoot a) :
    a < wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ a := by
  rcases ha with ha | ha | ha | rfl
  · left
    rcases ha with ⟨_, h⟩
    dsimp [consoleImpurePtrAddr, wrErrnoAddr] at *
    omega
  · left
    rcases ha with ⟨_, h⟩
    dsimp [consoleReent, wrErrnoAddr] at *
    omega
  · right
    rcases ha with ⟨h, _⟩
    dsimp [consoleStdout, wrErrnoAddr] at *
    omega
  · right
    dsimp [consoleBuf, wrErrnoAddr]
    omega

theorem sflushCallbackM_console_agree (g : SflushG) (hg : SflushGOk g)
    (a : Nat) (ha : ConsoleFoot a) :
    (sflushCallbackM g)[a]? = (sflushClosedM g)[a]? := by
  have hsw := sflushSWG_ok g hg
  have hwr := swWRG_ok (sflushSWG g) hsw
  have hbound := consoleFoot_lt_stdout_end a ha
  have hsp := sflush_spE_toNat g.sp hg.stack
  have hwrstep : (sflushCallbackM g)[a]? =
      (swM2 (sflushSWG g))[a]? := by
    unfold sflushCallbackM
    apply wrM1_getElem_lo (swWRG (sflushSWG g)) hwr a
    · left
      simp only [swWRG, sflushSWG]
      rw [hsp]
      have := hg.stack.callbackConsole
      omega
    · exact consoleFoot_errno_disjoint a ha
  by_cases h0 : a = consoleStdout + 16
  · subst a
    exact hwrstep.trans ((sflushSwM2_flag0 g hg).trans
      (sflushClosedM_console g hg).flag0.symm)
  by_cases h1 : a = consoleStdout + 17
  · subst a
    exact hwrstep.trans ((sflushSwM2_flag1 g hg).trans
      (sflushClosedM_console g hg).flag1.symm)
  · have hswstep := swM2_getElem_lo (sflushSWG g) hsw a
      (by
        left
        simp only [sflushSWG]
        rw [hsp]
        have := hg.stack.callbackConsole
        omega)
      (by
        change a < consoleStdout + 16 ∨ consoleStdout + 18 ≤ a
        omega)
    exact hwrstep.trans (by simpa [sflushSWG] using hswstep)

theorem sflushCallbackM_console (g : SflushG) (hg : SflushGOk g) :
    ConsoleStream (sflushCallbackM g) :=
  ConsoleStream.of_agree (sflushCallbackM_console_agree g hg)
    (sflushClosedM_console g hg)

end Vsa.Sim

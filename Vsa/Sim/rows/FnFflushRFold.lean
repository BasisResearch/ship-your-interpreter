import Vsa.Sim.WordLoadData
import Vsa.Sim.rows.FnFflushR
import Vsa.Sim.rows.FnLockStubsFold
import Vsa.Sim.rows.FnSflushRSuffix
import Vsa.Sim.ChainFactsTac

/-! # Concrete `_fflush_r` fold for initialized stdout -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

def fflushSpE (sp : BitVec 64) : BitVec 64 :=
  sp + sign_extend (m := 64) (0xfe0#12)

structure FflushStackOK (sp : BitVec 64) : Prop where
  nested : SflushStackOK (fflushSpE sp)
  lo : 32 ≤ sp.toNat
  hi : sp.toNat ≤ 0x100000000
  align : sp.toNat % 8 = 0

structure FflushG where
  ch : BitVec 8
  sp : BitVec 64
  ra : BitVec 64
  s0 : BitVec 64
  sv : SRegs
  m0 : Mem
  out0 : Array String

def fflushPrefixSeg : List BBlock :=
  fflush_rXedccFSeg ++ fflush_rXeddcFSeg ++ fflush_rXede4FSeg ++
  fflush_rXedf0FSeg ++ fflush_rXedfcTSeg ++ fflush_rXee04Seg

def fflushPrefixL (g : FflushG) : GRegs :=
  [(11, BitVec.ofNat 64 consoleStdout)] ++
    fflush_rXedccFL g.sp g.ra (BitVec.ofNat 64 consoleReent)

def fflushPrefixLds : List (List (BitVec 8)) :=
  [flushBytes8 (BitVec.ofNat 64 consoleSinit),
   [0x0a#8, 0x20#8], [0#8, 0#8, 0#8, 0#8]]

def fflushAcquireM (g : FflushG) : Mem :=
  writeMap8
    (writeMap8
      (writeMap8 g.m0
        (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat
        (sdData_val g.ra))
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
      (sdData_val (BitVec.ofNat 64 consoleReent)))
    (fflushSpE g.sp).toNat
    (sdData_val (BitVec.ofNat 64 consoleStdout))

def fflushPrefixM (g : FflushG) : Mem :=
  writeMap8 (fflushAcquireM g) (fflushSpE g.sp).toNat
    (sdData_val (BitVec.ofNat 64 consoleStdout))

def fflushSG (g : FflushG) : SflushG :=
  { ch := g.ch
    sp := fflushSpE g.sp
    ra := 0x8000ee10#64
    s0 := g.s0
    sv := g.sv
    m0 := fflushPrefixM g
    out0 := g.out0 }

def fflushAfterSflushM (g : FflushG) : Mem :=
  sflushCallbackM (fflushSG g)

def fflushReleaseM (g : FflushG) : Mem :=
  writeMap8 (fflushAfterSflushM g) (fflushSpE g.sp).toNat (sdData_val (0#64))

structure FflushGOk (g : FflushG) : Prop where
  stack : FflushStackOK g.sp
  ra_align : g.ra.toNat % 4 = 0
  console : ConsoleFlushState g.m0 g.ch
  codeF : Vsa.Sim.Code._fflush_rLoaded g.m0
  codeF_acquire : Vsa.Sim.Code._fflush_rLoaded (fflushAcquireM g)
  codeAcquire : Vsa.Sim.Code.__retarget_lock_acquire_recursiveLoaded
    (fflushAcquireM g)
  codeF_prefix : Vsa.Sim.Code._fflush_rLoaded (fflushPrefixM g)
  consolePrefix : ConsoleFlushState (fflushPrefixM g) g.ch
  codeSflush : Vsa.Sim.Code.__sflush_rLoaded (fflushPrefixM g)
  codeWrite : Vsa.Sim.Code._writeLoaded (fflushPrefixM g)
  codeWriteR : Vsa.Sim.Code._write_rLoaded (fflushPrefixM g)
  codeSwrite : Vsa.Sim.Code.__swriteLoaded (fflushPrefixM g)
  codeF_after : Vsa.Sim.Code._fflush_rLoaded (fflushAfterSflushM g)
  codeF_release : Vsa.Sim.Code._fflush_rLoaded (fflushReleaseM g)
  codeRelease : Vsa.Sim.Code.__retarget_lock_release_recursiveLoaded
    (fflushReleaseM g)

theorem fflushSG_ok (g : FflushG) (hg : FflushGOk g) :
    SflushGOk (fflushSG g) :=
  { stack := hg.stack.nested
    ra_align := by
      show (0x8000ee10#64).toNat % 4 = 0
      decide
    console := hg.consolePrefix
    codeF := hg.codeSflush
    codeW := hg.codeWrite
    codeR := hg.codeWriteR
    codeS := hg.codeSwrite }

theorem sflushClosedM_outer_entry (g : SflushG) (hg : SflushGOk g)
    (k : Nat) (hk : g.sp.toNat ≤ k) :
    (sflushClosedM g)[k]? = g.m0[k]? := by
  unfold sflushClosedM sflushM4 sflushM3 sflushM2
  rw [getElem_writeMap4_disjoint]
  · rw [getElem_writeMap8_disjoint]
    · rw [getElem_writeMap8_disjoint]
      · rw [getElem_writeMap8_disjoint]
        · unfold sflushM1
          apply writeLog_getElem_disjoint k (sflushEntryLog g.sp g.s0 g.sv.s3 g.ra)
          · intro e he
            simp only [sflushEntryLog, List.mem_cons] at he
            rcases he with rfl | rfl | rfl | h
            · simp
            · simp
            · simp
            · exact nomatch h
          · intro e he
            simp only [sflushEntryLog, List.mem_cons] at he
            rcases he with rfl | rfl | rfl | h
            · right
              change (sflushSpE g.sp + sign_extend (m := 64) (0x020#12)).toNat +
                8 ≤ k
              rw [show sign_extend (m := 64) (0x020#12) = 32#64 by decide,
                sflush_slot_toNat g.sp hg.stack 32 (by decide) (by decide)]
              have hc := hg.stack.console
              omega
            · right
              change (sflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat +
                8 ≤ k
              rw [show sign_extend (m := 64) (0x008#12) = 8#64 by decide,
                sflush_slot_toNat g.sp hg.stack 8 (by decide) (by decide)]
              have hc := hg.stack.console
              omega
            · right
              change (sflushSpE g.sp + sign_extend (m := 64) (0x028#12)).toNat +
                8 ≤ k
              rw [show sign_extend (m := 64) (0x028#12) = 40#64 by decide,
                sflush_slot_toNat g.sp hg.stack 40 (by decide) (by decide)]
              have hc := hg.stack.console
              omega
            · exact nomatch h
        · right
          rw [show sign_extend (m := 64) (0x010#12) = 16#64 by decide,
            sflush_slot_toNat g.sp hg.stack 16 (by decide) (by decide)]
          have hc := hg.stack.console
          omega
      · right
        rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
          sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide)]
        have hc := hg.stack.console
        omega
    · right
      have hc := hg.stack.console
      omega
  · right
    have hc := hg.stack.console
    omega

theorem sflushCallbackM_outer_entry (g : SflushG) (hg : SflushGOk g)
    (k : Nat) (hk : g.sp.toNat ≤ k) :
    (sflushCallbackM g)[k]? = g.m0[k]? :=
  (sflushCallbackM_outer g hg k (by
    rw [sflush_spE_toNat g.sp hg.stack]
    have hc := hg.stack.console
    omega)).trans (sflushClosedM_outer_entry g hg k hk)

theorem fflushAfter_slot0_pin (g : FflushG) (hg : FflushGOk g) :
    Pin8 (fflushAfterSflushM g) (fflushSpE g.sp).toNat
      (BitVec.ofNat 64 consoleStdout) := by
  have hp : Pin8 (fflushPrefixM g) (fflushSpE g.sp).toNat
      (BitVec.ofNat 64 consoleStdout) := by
    unfold fflushPrefixM
    exact Pin8_writeMap8 _ _ _
  apply Pin8_frame (a := (fflushSpE g.sp).toNat)
    (v := BitVec.ofNat 64 consoleStdout) _ hp
  intro k hk0 hk1
  exact sflushCallbackM_outer_entry (fflushSG g) (fflushSG_ok g hg) k hk0

private theorem fflush_lpins8_of_pin {m : Mem} {a : Nat} {v : BitVec 64}
    (hp : Pin8 m a v) : LPins8 m a (flushBytes8 v) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := hp
  exact ⟨lpin_of_present p0, lpin_of_present p1, lpin_of_present p2,
    lpin_of_present p3, lpin_of_present p4, lpin_of_present p5,
    lpin_of_present p6, lpin_of_present p7⟩

private theorem fflush_lpins8_zero {m : Mem} {a : Nat}
    (h : read64 m a = some 0) : LPins8 m a (flushBytes8 (0#64)) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
    h0, h1, h2, h3, h4, h5, h6, h7, hv⟩ := read64_bytes m a 0 h
  have z0 := b0.isLt; have z1 := b1.isLt; have z2 := b2.isLt; have z3 := b3.isLt
  have z4 := b4.isLt; have z5 := b5.isLt; have z6 := b6.isLt; have z7 := b7.isLt
  have q0 : b0 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b0.toNat = 0; omega
  have q1 : b1 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b1.toNat = 0; omega
  have q2 : b2 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b2.toNat = 0; omega
  have q3 : b3 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b3.toNat = 0; omega
  have q4 : b4 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b4.toNat = 0; omega
  have q5 : b5 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b5.toNat = 0; omega
  have q6 : b6 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b6.toNat = 0; omega
  have q7 : b7 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b7.toNat = 0; omega
  subst b0; subst b1; subst b2; subst b3; subst b4; subst b5; subst b6; subst b7
  exact ⟨lpin_of_present h0, lpin_of_present h1, lpin_of_present h2,
    lpin_of_present h3, lpin_of_present h4, lpin_of_present h5,
    lpin_of_present h6, lpin_of_present h7⟩

def fflushEe10Lds : List (List (BitVec 8)) :=
  [flushBytes8 (BitVec.ofNat 64 consoleStdout), [0#8, 0#8, 0#8, 0#8]]

def fflushEe10Block : BBlock :=
  { body :=
      [(mkLine 0x8000ee10#64 0x00013583#32),
       (mkLine 0x8000ee14#64 0x00050793#32),
       (mkLine 0x8000ee18#64 0x0b05a703#32),
       (mkLine 0x8000ee1c#64 0x00177713#32)]
    term := some ⟨0x8000ee20#64, 0x00071863#32,
      0x63#8, 0x18#8, 0x07#8, 0x00#8,
      .br bop.BNE false, 14, 0, 0x0010#13, 0#21, 0#12⟩ }

theorem fflushEe10Seg_eq : fflush_rXee10FSeg = [fflushEe10Block] := rfl

private theorem progFactsM_cons {mc m : Mem} {L : GRegs}
    {lds : List (List (BitVec 8))} {a : MInstr} {r : List MInstr}
    (hp : BytePinsM mc a) (hd : DecodeFactM a)
    (hm : MemFacts m L (lds.headD []) a)
    (ht : ProgFactsM mc (stepMemM m a L)
      (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) r) :
    ProgFactsM mc m L lds (a :: r) :=
  ⟨hp, hd, hm, ht⟩

/-
theorem fflushEe10_prog_facts (g : FflushG) (hg : FflushGOk g) :
    ProgFactsM (fflushAfterSflushM g) (fflushAfterSflushM g)
      (fflush_rXee10FL (fflushSpE g.sp) (0#64)) fflushEe10Lds
      fflushEe10Block.body := by
  unfold fflushEe10Block
  apply progFactsM_cons
  · exact Vsa.Sim.Code._fflush_r_at_8000ee10 hg.codeF_after
  · exact Vsa.Sim.DecodeTable.decode_00013583
  · refine ⟨fflush_store0_range g.sp hg.stack, ?_⟩
    exact fflush_lpins8_of_pin (fflushAfter_slot0_pin g hg)
  apply progFactsM_cons
  · exact Vsa.Sim.Code._fflush_r_at_8000ee14 hg.codeF_after
  · exact Vsa.Sim.DecodeTable.decode_00050793
  · trivial
  apply progFactsM_cons
  · exact Vsa.Sim.Code._fflush_r_at_8000ee18 hg.codeF_after
  · exact Vsa.Sim.DecodeTable.decode_0b05a703
  · have hc := sflushCallbackM_console (fflushSG g) (fflushSG_ok g hg)
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    exact fflush_lpins4_zero hc.lockMode
  apply progFactsM_cons
  · exact Vsa.Sim.Code._fflush_r_at_8000ee1c hg.codeF_after
  · exact Vsa.Sim.DecodeTable.decode_00177713
  · trivial
  trivial
-/

/-
theorem fflushEe10_facts (g : FflushG) (hg : FflushGOk g) :
    ChainFacts (fflushAfterSflushM g) (fflushAfterSflushM g)
      (fflush_rXee10FL (fflushSpE g.sp) (0#64)) fflushEe10Lds
      fflush_rXee10FSeg := by
  chain_facts hg.codeF_after with "Vsa.Sim.Code._fflush_r_at_"
  · refine ⟨fflush_store0_range g.sp hg.stack, ?_⟩
    exact fflush_lpins8_of_pin (fflushAfter_slot0_pin g hg)
  · have hc := sflushCallbackM_console (fflushSG g) (fflushSG_ok g hg)
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    exact fflush_lpins4_zero hc.lockMode
  · change guardB bop.BNE
      (bytesVal MKind.lw [0#8, 0#8, 0#8, 0#8] &&&
        sign_extend (m := 64) (0x001#12)) (0#64) = false
    decide
-/

theorem fflush_spE_toNat (sp : BitVec 64) (hs : FflushStackOK sp) :
    (fflushSpE sp).toNat = sp.toNat - 32 := by
  refine ptr_sub_toNat sp (0xfe0#12) 32 ?_ ?_
  · decide
  · exact hs.lo

theorem fflush_slot_toNat (sp : BitVec 64) (hs : FflushStackOK sp)
    (off : Nat) (hoff : off ≤ 32) :
    (fflushSpE sp + BitVec.ofNat 64 off).toNat = sp.toNat - 32 + off := by
  have he := fflush_spE_toNat sp hs
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : off < 2 ^ 64), he]
  apply Nat.mod_eq_of_lt
  have := hs.hi
  omega

theorem fflushEdcc_facts (g : FflushG) (hg : FflushGOk g) :
    ChainFacts g.m0 g.m0 (fflushPrefixL g) fflushPrefixLds
      fflush_rXedccFSeg := by
  chain_facts hg.codeF with "Vsa.Sim.Code._fflush_r_at_"
  · show 0x80000000 ≤
        (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤
        0x100000000 ∧
      tohostAddr + 16 ≤
        (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have hn := hg.stack.nested.htif
    have he := fflush_spE_toNat g.sp hg.stack
    rw [he] at hn
    have := hg.stack.hi
    have := hg.stack.align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · rfl

def fflushL1 (g : FflushG) : GRegs :=
  [(14, BitVec.ofNat 64 consoleReent), (2, fflushSpE g.sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, g.ra),
   (10, BitVec.ofNat 64 consoleReent)]

def fflushM1 (g : FflushG) : Mem :=
  memChain fflush_rXedccFSeg g.m0 (fflushPrefixL g) fflushPrefixLds

def fflushLds1 : List (List (BitVec 8)) :=
  fflushPrefixLds

theorem fflushM1_eq (g : FflushG) :
    fflushM1 g =
      writeMap8 g.m0
        (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat
        (sdData_val g.ra) := rfl

private theorem fflush_lpins8_of_read64 {m : Mem} {a p : Nat}
    (e0 e1 e2 e3 e4 e5 e6 e7 : BitVec 8)
    (h : read64 m a = some p)
    (hep : e0.toNat + 256 * (e1.toNat + 256 * (e2.toNat + 256 *
      (e3.toNat + 256 * (e4.toNat + 256 * (e5.toNat + 256 *
      (e6.toNat + 256 * e7.toNat)))))) = p) :
    LPins8 m a [e0, e1, e2, e3, e4, e5, e6, e7] := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
    h0, h1, h2, h3, h4, h5, h6, h7, hv⟩ := read64_bytes m a p h
  have hb0 := b0.isLt; have hb1 := b1.isLt; have hb2 := b2.isLt
  have hb3 := b3.isLt; have hb4 := b4.isLt; have hb5 := b5.isLt
  have hb6 := b6.isLt; have hb7 := b7.isLt
  have he0 := e0.isLt; have he1 := e1.isLt; have he2 := e2.isLt
  have he3 := e3.isLt; have he4 := e4.isLt; have he5 := e5.isLt
  have he6 := e6.isLt; have he7 := e7.isLt
  have q0 : b0 = e0 := by apply BitVec.eq_of_toNat_eq; omega
  have q1 : b1 = e1 := by apply BitVec.eq_of_toNat_eq; omega
  have q2 : b2 = e2 := by apply BitVec.eq_of_toNat_eq; omega
  have q3 : b3 = e3 := by apply BitVec.eq_of_toNat_eq; omega
  have q4 : b4 = e4 := by apply BitVec.eq_of_toNat_eq; omega
  have q5 : b5 = e5 := by apply BitVec.eq_of_toNat_eq; omega
  have q6 : b6 = e6 := by apply BitVec.eq_of_toNat_eq; omega
  have q7 : b7 = e7 := by apply BitVec.eq_of_toNat_eq; omega
  subst b0; subst b1; subst b2; subst b3; subst b4; subst b5; subst b6; subst b7
  unfold LPins8
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨lpin_of_present h0, lpin_of_present h1, lpin_of_present h2,
    lpin_of_present h3, lpin_of_present h4, lpin_of_present h5,
    lpin_of_present h6, lpin_of_present h7⟩

theorem fflushEddc_facts (g : FflushG) (hg : FflushGOk g) :
    ChainFacts g.m0 (fflushM1 g) (fflushL1 g) fflushLds1
      fflush_rXeddcFSeg := by
  chain_facts hg.codeF with "Vsa.Sim.Code._fflush_r_at_"
  · have ha : eaddrM (mkLine 0x8000eddc#64 0x04853783#32)
        (fflushL1 g) = BitVec.ofNat 64 (consoleReent + 72) := rfl
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha]; decide
    · rw [ha]; decide
    · rw [ha]; decide
    change LPins8 (fflushM1 g) (consoleReent + 72)
      (flushBytes8 (BitVec.ofNat 64 consoleSinit))
    rw [fflushM1_eq]
    refine lpins8_writeMap8_disjoint _ _ ?_ ?_
    · left
      rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
        fflush_slot_toNat g.sp hg.stack 24 (by decide)]
      have hn := hg.stack.nested.console
      have he := fflush_spE_toNat g.sp hg.stack
      rw [he] at hn
      dsimp [consoleReent, consoleStdout] at *
      omega
    · apply fflush_lpins8_of_read64 _ _ _ _ _ _ _ _ hg.console.sinit
      decide
  · rfl

def fflushL2 (g : FflushG) : GRegs :=
  [(15, BitVec.ofNat 64 consoleSinit),
   (14, BitVec.ofNat 64 consoleReent), (2, fflushSpE g.sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, g.ra),
   (10, BitVec.ofNat 64 consoleReent)]

def fflushLds2 : List (List (BitVec 8)) :=
  [[0x0a#8, 0x20#8], [0#8, 0#8, 0#8, 0#8]]

theorem fflushEde4_facts (g : FflushG) (hg : FflushGOk g) :
    ChainFacts g.m0 (fflushM1 g) (fflushL2 g) fflushLds2
      fflush_rXede4FSeg := by
  chain_facts hg.codeF with "Vsa.Sim.Code._fflush_r_at_"
  · have ha : eaddrM (mkLine 0x8000ede4#64 0x01059683#32)
        (fflushL2 g) = BitVec.ofNat 64 (consoleStdout + 16) := rfl
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [ha]; decide
    · rw [ha]; decide
    · rw [ha]; decide
    · rw [ha]
      change ((fflushM1 g)[consoleStdout + 16]?).getD 0 = 0x0a#8
      rw [fflushM1_eq, getElem_writeMap8_disjoint]
      · exact lpin_of_present hg.console.flag0
      · left
        rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
          fflush_slot_toNat g.sp hg.stack 24 (by decide)]
        have hn := hg.stack.nested.console
        have he := fflush_spE_toNat g.sp hg.stack
        rw [he] at hn
        dsimp [consoleStdout] at *
        omega
    · rw [ha]
      change ((fflushM1 g)[consoleStdout + 17]?).getD 0 = 0x20#8
      rw [fflushM1_eq, getElem_writeMap8_disjoint]
      · exact lpin_of_present hg.console.flag1
      · left
        rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
          fflush_slot_toNat g.sp hg.stack 24 (by decide)]
        have hn := hg.stack.nested.console
        have he := fflush_spE_toNat g.sp hg.stack
        rw [he] at hn
        dsimp [consoleStdout] at *
        omega
  · rfl

private theorem fflush_lpins4_zero {m : Mem} {a : Nat}
    (h : read32 m a = some 0) : LPins4 m a [0#8, 0#8, 0#8, 0#8] := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, hv⟩ := read32_bytes m a 0 h
  have hb0 := b0.isLt; have hb1 := b1.isLt
  have hb2 := b2.isLt; have hb3 := b3.isLt
  have q0 : b0 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b0.toNat = 0; omega
  have q1 : b1 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b1.toNat = 0; omega
  have q2 : b2 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b2.toNat = 0; omega
  have q3 : b3 = 0#8 := by apply BitVec.eq_of_toNat_eq; change b3.toNat = 0; omega
  subst b0; subst b1; subst b2; subst b3
  exact ⟨lpin_of_present h0, lpin_of_present h1,
    lpin_of_present h2, lpin_of_present h3⟩

private theorem fflush_lpins4_write8 {m : Mem} {base a : Nat}
    (d : BitVec 64) (hdis : base + 4 ≤ a ∨ a + 8 ≤ base)
    (hp : LPins4 m base [0#8, 0#8, 0#8, 0#8]) :
    LPins4 (writeMap8 m a (sdData_val d)) base [0#8, 0#8, 0#8, 0#8] := by
  obtain ⟨p0, p1, p2, p3⟩ := hp
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by rcases hdis with h | h <;> omega)]; exact p0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by rcases hdis with h | h <;> omega)]; exact p1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by rcases hdis with h | h <;> omega)]; exact p2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by rcases hdis with h | h <;> omega)]; exact p3⟩

def fflushL3 (g : FflushG) : GRegs :=
  [(15, 0#64), (13, 0x200a#64),
   (14, BitVec.ofNat 64 consoleReent), (2, fflushSpE g.sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, g.ra),
   (10, BitVec.ofNat 64 consoleReent)]

def fflushLds3 : List (List (BitVec 8)) :=
  [[0#8, 0#8, 0#8, 0#8]]

theorem fflushEdf0_facts (g : FflushG) (hg : FflushGOk g) :
    ChainFacts g.m0 (fflushM1 g) (fflushL3 g) fflushLds3
      fflush_rXedf0FSeg := by
  chain_facts hg.codeF with "Vsa.Sim.Code._fflush_r_at_"
  · have ha : eaddrM (mkLine 0x8000edf0#64 0x0b05a783#32)
        (fflushL3 g) = BitVec.ofNat 64 (consoleStdout + 176) := rfl
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha]; decide
    · rw [ha]; decide
    · rw [ha]; decide
    · change LPins4 (fflushM1 g) (consoleStdout + 176) [0#8, 0#8, 0#8, 0#8]
      rw [fflushM1_eq]
      refine fflush_lpins4_write8 _ ?_ (fflush_lpins4_zero hg.console.lockMode)
      left
      rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
        fflush_slot_toNat g.sp hg.stack 24 (by decide)]
      have hn := hg.stack.nested.console
      have he := fflush_spE_toNat g.sp hg.stack
      rw [he] at hn
      dsimp [consoleStdout] at *
      omega
  · have hz : bytesVal MKind.lw [0#8, 0#8, 0#8, 0#8] = (0#64) := by decide
    have h15 : srcVal 15
        (runGM [(mkLine 0x8000edf0#64 0x0b05a783#32),
          (mkLine 0x8000edf4#64 0x0017f793#32)]
          (fflushL3 g) fflushLds3) = 0#64 := by
      change (bytesVal MKind.lw [0#8, 0#8, 0#8, 0#8] &&&
        sign_extend (m := 64) (0x001#12)) = 0#64
      rw [hz]
      decide
    have h0 : srcVal 0
        (runGM [(mkLine 0x8000edf0#64 0x0b05a783#32),
          (mkLine 0x8000edf4#64 0x0017f793#32)]
          (fflushL3 g) fflushLds3) = 0#64 := by rfl
    rw [h15, h0]
    decide

def fflushL4 (g : FflushG) : GRegs := fflushL3 g

def fflushL5 (g : FflushG) : GRegs :=
  [(13, 0#64), (15, 0#64),
   (14, BitVec.ofNat 64 consoleReent), (2, fflushSpE g.sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, g.ra),
   (10, BitVec.ofNat 64 consoleReent)]

theorem fflushEdFcT_facts (g : FflushG)
    (hcode : Vsa.Sim.Code._fflush_rLoaded g.m0) :
    ChainFacts g.m0 (fflushM1 g) (fflushL4 g) [] fflush_rXedfcTSeg := by
  chain_facts hcode with "Vsa.Sim.Code._fflush_r_at_"
  · change guardB bop.BEQ
      (0x200a#64 &&& sign_extend (m := 64) (0x200#12)) 0#64 = true
    decide

def fflushL6 (g : FflushG) : GRegs :=
  [(10, BitVec.ofNat 64 consoleReent),
   (13, 0#64), (15, 0#64),
   (14, BitVec.ofNat 64 consoleReent), (2, fflushSpE g.sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, g.ra)]

def fflushEe04L (sp ra : BitVec 64) : GRegs :=
  [(13, 0#64), (15, 0#64),
   (14, BitVec.ofNat 64 consoleReent), (2, fflushSpE sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, ra),
   (10, BitVec.ofNat 64 consoleReent)]

def fflushEe04Block : BBlock :=
  { body := [(mkLine 0x8000ee04#64 0x00070513#32),
      (mkLine 0x8000ee08#64 0x00b13023#32)]
    term := none }

theorem fflushEe04Seg_eq : fflush_rXee04Seg = [fflushEe04Block] := rfl

theorem fflush_store0_range (sp : BitVec 64) (hs : FflushStackOK sp) :
    0x80000000 ≤ (fflushSpE sp).toNat ∧
    (fflushSpE sp).toNat + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (fflushSpE sp).toNat ∧
    (fflushSpE sp).toNat % 8 = 0 := by
  have he := fflush_spE_toNat sp hs
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hn := hs.nested.htif
  have hh := hs.hi
  have ha := hs.align
  rw [he] at hn
  rw [he]
  exact ⟨by omega, by omega, by omega, by omega⟩

def fflushEe08L (sp ra : BitVec 64) : GRegs :=
  [(10, BitVec.ofNat 64 consoleReent),
   (13, 0#64), (15, 0#64),
   (14, BitVec.ofNat 64 consoleReent), (2, fflushSpE sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, ra)]

theorem fflushEe04_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee04#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (v14 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee04 hmem
  exact stepObs_alu σ i u (0x8000ee04#64) vminstret (0x00070513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0e#5,
      regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v14 + sign_extend (m := 64) (0x000#12))
    (0x13#8) (0x05#8) (0x07#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00070513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0e#5)
      (regidx.Regidx 0x0a#5) v14
      (afterNextPC (afterPrelude σ) (0x8000ee04#64))
      (sigma3_alu σ (0x8000ee04#64) Register.x10
        (v14 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x8000ee04#64) _ (by decide) (by decide)]
            exact hx14))
      (wX_bits_x10 _ (v14 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem fflushEe08_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee08#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤
      0x100000000)
    (hahiwin : tohostAddr + 16 ≤
      (vsp + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000ee08#64)).mem
        (vsp + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v11) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000ee08#64)).mem
            (vsp + sign_extend (m := 64) (0x000#12)).toNat
            (sdData_val v11))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee08 hmem
  have hx2' : (afterNextPC (afterPrelude σ) (0x8000ee08#64)).regs.get?
      Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x8000ee08#64) _ (by decide) (by decide)]
    exact hx2
  have hx11' : (afterNextPC (afterPrelude σ) (0x8000ee08#64)).regs.get?
      Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x8000ee08#64) _ (by decide) (by decide)]
    exact hx11
  exact stepObs_store σ i u (0x8000ee08#64) vminstret (0x00b13023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0b#5,
      regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000ee08#64)).mem
      (vsp + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v11))
    (0x23#8) (0x30#8) (0xb1#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00b13023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000ee08#64) (0x000#12)
      (regidx.Regidx 0x0b#5) (regidx.Regidx 0x02#5)
      vsp v11 hG (rX_bits_x2 _ vsp hx2') (rX_bits_x11 _ v11 hx11')
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem fflushEe08_site_zero (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee08#64 : BitVec 64))
    (halo : 0x80000000 ≤ vsp.toNat)
    (hahiram : vsp.toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ vsp.toNat)
    (haalign : vsp.toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 σ.mem vsp.toNat (sdData_val v11) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 σ.mem vsp.toNat (sdData_val v11))) := by
  obtain ⟨σ', i', hs, hi', hG', hm, ho⟩ :=
    fflushEe08_site σ i u pc vminstret vsp v11 hG hpc hminstret hx2 hx11
      hmem hpcv
      (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide] using halo)
      (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide] using hahiram)
      (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide] using hahiwin)
      (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide] using haalign)
      hi
  refine ⟨σ', i', hs, hi', hG', ?_, ?_⟩
  · simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide] using hm
  · simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide] using ho

def fflushAcquireKeep (g : FflushG) : GRegs :=
  [(10, 0#64), (11, BitVec.ofNat 64 consoleStdout),
   (14, BitVec.ofNat 64 consoleReent), (2, fflushSpE g.sp),
   (3, wrGpVal), (8, g.s0)] ++ sKeepL g.sv

structure FflushAtAcquire (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushAcquireM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee4c#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  ra : gprGet c.σ 1 = some g.ra
  keep : GHolds c.σ (fflushAcquireKeep g)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

theorem fflushAcquireJalArm (g : FflushG) :
    Triple (FflushAtAcquire g)
      (fun c => PCAt 0x80006fe0#64 c ∧
        RetStubPre 0x8000ee50#64 (fflushAcquireKeep g)
          (fflushAcquireM g) g.out0 (0#4) c) := by
  intro c hA
  obtain ⟨vm1, hmi1⟩ := hA.minstret
  have hcF : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hA.mem]
    exact hA.ok.codeF_acquire
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee4c hcF
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000ee4c#64) vm1 (0x994f80ef#32)
      (0x1f8194#21) (regidx.Regidx 0x01#5) Register.x1
      (BitVec.addInt (0x8000ee4c#64) 4)
      (0xef#8) (0x80#8) (0x4f#8) (0x99#8)
      hA.good hA.pc hmi1 hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_994f80ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000ee4c#64) 4)) hA.tick
  refine ⟨⟨σ2, i2, c.steps + 1⟩, Steps.head hstep (Steps.refl _), ?_, ?_⟩
  · show σ2.regs.get? Register.PC = some 0x80006fe0#64
    rw [obs_jal_pc_env hobs]
    rw [show (0x8000ee4c#64 + sign_extend (m := 64) (0x1f8194#21) : BitVec 64)
      = 0x80006fe0#64 from by decide]
  · have hra := obs_jal_rd_env hobs (by decide) (by decide) (by decide)
        (by decide) (by decide)
    have hra' : gprGet σ2 1 = some 0x8000ee50#64 := by
      rwa [show BitVec.addInt (0x8000ee4c#64) 4 = 0x8000ee50#64 from by decide]
        at hra
    obtain ⟨ka0, ka1, ka4, ksp, kgp, ks0,
      k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hA.keep
    exact
      { good := hG2
        tick := hi2
        mem := hmem2.trans hA.mem
        minstret := obs_jal_minstret_env hobs
        ra := hra'
        keep := ⟨
          obs_jal_other_env hobs Register.x10 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) ka0,
          obs_jal_other_env hobs Register.x11 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) ka1,
          obs_jal_other_env hobs Register.x14 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) ka4,
          obs_jal_other_env hobs Register.x2 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) ksp,
          obs_jal_other_env hobs Register.x3 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) kgp,
          obs_jal_other_env hobs Register.x8 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) ks0,
          obs_jal_other_env hobs Register.x9 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k1,
          obs_jal_other_env hobs Register.x18 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k2,
          obs_jal_other_env hobs Register.x19 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k3,
          obs_jal_other_env hobs Register.x20 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k4,
          obs_jal_other_env hobs Register.x21 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k5,
          obs_jal_other_env hobs Register.x22 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k6,
          obs_jal_other_env hobs Register.x23 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k7,
          obs_jal_other_env hobs Register.x24 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k8,
          obs_jal_other_env hobs Register.x25 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k9,
          obs_jal_other_env hobs Register.x26 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k10,
          obs_jal_other_env hobs Register.x27 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k11,
          trivial⟩
        out := hobs.2.trans ((sailOutput_sigmaPost_jal c.σ (0x8000ee4c#64) vm1
          (0x1f8194#21) Register.x1 (BitVec.addInt (0x8000ee4c#64) 4)).trans hA.out)
        pw := obs_jal_other_env hobs Register.htif_payload_writes (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) hA.pw
        th := by
          obtain ⟨v, hv⟩ := hA.th
          exact ⟨v, obs_jal_other_env hobs Register.htif_tohost (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) hv⟩ }

theorem fflushAcquireArm (g : FflushG) :
    Triple (FflushAtAcquire g)
      (RetStubPost 0x8000ee50#64 (fflushAcquireKeep g)
        (fflushAcquireM g) g.out0 (0#4)) := by
  intro c hc
  obtain ⟨c1, hs1, h1⟩ := fflushAcquireJalArm g c hc
  have T := lockAcquire_summary 0x8000ee50#64 (fflushAcquireKeep g)
    (fflushAcquireM g) g.out0 (0#4)
    (by
      change FrameOK [10, 11, 14, 2, 3, 8, 9, 18, 19, 20, 21, 22, 23,
        24, 25, 26, 27] retarget_lock_acquire_recursiveX6fe0Seg
      decide)
    hc.ok.codeAcquire
    (by apply BitVec.eq_of_toNat_eq; decide) (by decide)
  obtain ⟨c2, hs2, h2⟩ := T.run c1 h1
  exact ⟨c2, Steps.trans hs1 hs2, h2⟩

theorem fflushAcquire_slot0_pin (g : FflushG) :
    Pin8 (fflushAcquireM g) (fflushSpE g.sp).toNat
      (BitVec.ofNat 64 consoleStdout) := by
  unfold fflushAcquireM
  exact Pin8_writeMap8 _ _ _

theorem fflushAcquire_slot8_pin (g : FflushG) (hg : FflushGOk g) :
    Pin8 (fflushAcquireM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
      (BitVec.ofNat 64 consoleReent) := by
  unfold fflushAcquireM
  let mprev := writeMap8
    (writeMap8 g.m0
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat
      (sdData_val g.ra))
    (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
    (sdData_val (BitVec.ofNat 64 consoleReent))
  change Pin8 (writeMap8 mprev (fflushSpE g.sp).toNat
    (sdData_val (BitVec.ofNat 64 consoleStdout)))
    (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
    (BitVec.ofNat 64 consoleReent)
  apply Pin8_frame (mem := mprev) (a :=
    (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat)
    (v := BitVec.ofNat 64 consoleReent) _ (Pin8_writeMap8 _ _ _)
  intro k hk0 hk1
  rw [getElem_writeMap8_disjoint]
  rw [show sign_extend (m := 64) (0x008#12) = 8#64 by decide,
    fflush_slot_toNat g.sp hg.stack 8 (by decide)] at hk0
  rw [fflush_spE_toNat g.sp hg.stack]
  omega

def fflushEe50Lds : List (List (BitVec 8)) :=
  [flushBytes8 (BitVec.ofNat 64 consoleReent),
   flushBytes8 (BitVec.ofNat 64 consoleStdout)]

/-
theorem fflushEe50_facts (g : FflushG) (hg : FflushGOk g) :
    ChainFacts (fflushAcquireM g) (fflushAcquireM g)
      (fflush_rXee50L (fflushSpE g.sp)) fflushEe50Lds
      fflush_rXee50Seg := by
  chain_facts hg.codeF_acquire with "Vsa.Sim.Code._fflush_r_at_"
  · refine ⟨?_, fflush_lpins8_of_pin (fflushAcquire_slot8_pin g hg)⟩
    rw [show sign_extend (m := 64) (0x008#12) = 8#64 by decide]
    have h := fflush_store0_range g.sp hg.stack
    rw [fflush_slot_toNat g.sp hg.stack 8 (by decide)]
    rw [fflush_spE_toNat g.sp hg.stack] at h
    exact ⟨by omega, by omega, by omega, by omega⟩
  · exact ⟨fflush_store0_range g.sp hg.stack,
      fflush_lpins8_of_pin (fflushAcquire_slot0_pin g)⟩
-/

theorem fflushEe10_ld_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hsp : σ.regs.get? Register.x2 = some vsp)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee10#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11
        (sign_extend (m := 64)
          (bytesT8 σ.mem (vsp + sign_extend (m := 64) (0x000#12)).toNat :
            BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee10 hmem
  exact stepObs_alu σ i u (0x8000ee10#64) vminstret (0x00013583#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x02#5,
      regidx.Regidx 0x0b#5, false, 8))
    Register.x11
    (sign_extend (m := 64)
      (bytesT8 σ.mem (vsp + sign_extend (m := 64) (0x000#12)).toNat :
        BitVec (8 * 8)))
    (0x83#8) (0x35#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00013583 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_tot σ (0x8000ee10#64) (0x000#12)
      (regidx.Regidx 0x02#5) (regidx.Regidx 0x0b#5)
      (sigma3_alu σ (0x8000ee10#64) Register.x11
        (sign_extend (m := 64)
          (bytesT8 σ.mem (vsp + sign_extend (m := 64) (0x000#12)).toNat :
            BitVec (8 * 8)))) vsp hG
      (rX_bits_x2 _ vsp
        (by rw [get?_afterNextPC σ (0x8000ee10#64) _ (by decide) (by decide)]
            exact hsp))
      (wX_bits_x11 _
        (sign_extend (m := 64)
          (bytesT8 σ.mem (vsp + sign_extend (m := 64) (0x000#12)).toNat :
            BitVec (8 * 8)))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushPersist (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

structure FflushAtJal (g : FflushG) (c : Config) extends FflushPersist g c where
  mem : c.σ.mem = fflushPrefixM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee0c#64
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  ra : gprGet c.σ 1 = some 0x8000ee50#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe04 (g : FflushG) (c : Config) extends FflushPersist g c where
  mem : c.σ.mem = fflushAcquireM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee04#64
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  ra : gprGet c.σ 1 = some 0x8000ee50#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe08 (g : FflushG) (c : Config) extends FflushPersist g c where
  mem : c.σ.mem = fflushAcquireM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee08#64
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  ra : gprGet c.σ 1 = some 0x8000ee50#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

theorem fflushPersist_alu10 (g : FflushG) (c c' : Config)
    {pc vm v : BitVec 64} (hp : FflushPersist g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2)
    (hobs : ReadsLikePost c'.σ
      (sigmaPost_alu c.σ pc vm Register.x10 v)) :
    FflushPersist g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok
      good := hG
      tick := hi
      minstret := obs_alu_minstret hobs
      gp := obs_alu_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_alu_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨
        obs_alu_other' hobs Register.x9 (by decide) k1,
        obs_alu_other' hobs Register.x18 (by decide) k2,
        obs_alu_other' hobs Register.x19 (by decide) k3,
        obs_alu_other' hobs Register.x20 (by decide) k4,
        obs_alu_other' hobs Register.x21 (by decide) k5,
        obs_alu_other' hobs Register.x22 (by decide) k6,
        obs_alu_other' hobs Register.x23 (by decide) k7,
        obs_alu_other' hobs Register.x24 (by decide) k8,
        obs_alu_other' hobs Register.x25 (by decide) k9,
        obs_alu_other' hobs Register.x26 (by decide) k10,
        obs_alu_other' hobs Register.x27 (by decide) k11,
        trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_alu_other' hobs Register.htif_payload_writes (by decide) hp.pw
      th := ⟨thv, obs_alu_other' hobs Register.htif_tohost (by decide) hth⟩ }

theorem fflushPersist_store (g : FflushG) (c c' : Config)
    {pc vm : BitVec 64} {m : Mem} (hp : FflushPersist g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2)
    (hobs : ReadsLikePost c'.σ (sigmaPost_store c.σ pc vm m)) :
    FflushPersist g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok
      good := hG
      tick := hi
      minstret := obs_store_minstret hobs
      gp := obs_store_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_store_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨
        obs_store_other' hobs Register.x9 (by decide) k1,
        obs_store_other' hobs Register.x18 (by decide) k2,
        obs_store_other' hobs Register.x19 (by decide) k3,
        obs_store_other' hobs Register.x20 (by decide) k4,
        obs_store_other' hobs Register.x21 (by decide) k5,
        obs_store_other' hobs Register.x22 (by decide) k6,
        obs_store_other' hobs Register.x23 (by decide) k7,
        obs_store_other' hobs Register.x24 (by decide) k8,
        obs_store_other' hobs Register.x25 (by decide) k9,
        obs_store_other' hobs Register.x26 (by decide) k10,
        obs_store_other' hobs Register.x27 (by decide) k11,
        trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_store_other' hobs Register.htif_payload_writes (by decide) hp.pw
      th := ⟨thv, obs_store_other' hobs Register.htif_tohost (by decide) hth⟩ }

structure FflushEe04Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee04#64) vm Register.x10
      (BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x000#12)))

theorem fflushEe04Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe04 g c) :
    ∃ vm c1, FflushEe04Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_acquire
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe04_site c.σ c.tick c.steps (0x8000ee04#64) vm
      (BitVec.ofNat 64 consoleReent) hc.good hc.pc hmi hc.a4 hcode rfl hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩,
    { 
      step := hs1
      good := hG1
      tick := hi1
      mem := hmem1
      obs := hobs1 }⟩

theorem fflushEe04Step_persist (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hc : FflushAtEe04 g c)
    (hs : FflushEe04Step g c vm c1) : FflushPersist g c1 :=
  fflushPersist_alu10 g c c1 hc.toFflushPersist hs.good hs.tick hs.obs

theorem fflushEe04Step_mem (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hc : FflushAtEe04 g c)
    (hs : FflushEe04Step g c vm c1) : c1.σ.mem = fflushAcquireM g :=
  hs.mem.trans hc.mem

theorem fflushEe04Step_pc (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hs : FflushEe04Step g c vm c1) :
    c1.σ.regs.get? Register.PC = some 0x8000ee08#64 := by
  have h := obs_alu_pc hs.obs
  rwa [show BitVec.addInt (0x8000ee04#64) 4 = 0x8000ee08#64 from by decide] at h

theorem fflushEe04Step_a0 (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hs : FflushEe04Step g c vm c1) :
    gprGet c1.σ 10 = some (BitVec.ofNat 64 consoleReent) := by
  have h := obs_gpr_rd 10 (by decide) (by decide)
    (BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x000#12)) hs.obs
  rwa [show BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x000#12) =
    BitVec.ofNat 64 consoleReent from by decide] at h

theorem fflushEe04Step_a1 (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hc : FflushAtEe04 g c)
    (hs : FflushEe04Step g c vm c1) :
    gprGet c1.σ 11 = some (BitVec.ofNat 64 consoleStdout) :=
  obs_alu_other' hs.obs Register.x11 (by decide) hc.a1

theorem fflushEe04Step_ra (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hc : FflushAtEe04 g c)
    (hs : FflushEe04Step g c vm c1) :
    gprGet c1.σ 1 = some 0x8000ee50#64 :=
  obs_alu_other' hs.obs Register.x1 (by decide) hc.ra

theorem fflushEe04Step_sp (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hc : FflushAtEe04 g c)
    (hs : FflushEe04Step g c vm c1) :
    gprGet c1.σ 2 = some (fflushSpE g.sp) :=
  obs_alu_other' hs.obs Register.x2 (by decide) hc.sp

structure FflushEe08Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (m : Mem) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = m
  expected : m = writeMap8 c.σ.mem (fflushSpE g.sp).toNat
    (sdData_val (BitVec.ofNat 64 consoleStdout))
  obs : ReadsLikePost c1.σ
    (sigmaPost_store c.σ (0x8000ee08#64) vm m)

theorem fflushEe08Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe08 g c) :
    ∃ vm m c1, FflushEe08Step g c vm m c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_acquire
  have hrange := fflush_store0_range g.sp hc.ok.stack
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe08_site_zero c.σ c.tick c.steps (0x8000ee08#64) vm
      (fflushSpE g.sp) (BitVec.ofNat 64 consoleStdout)
      hc.good hc.pc hmi hc.sp hc.a1 hcode rfl
      hrange.1 hrange.2.1 hrange.2.2.1 hrange.2.2.2 hc.tick
  exact ⟨vm,
    writeMap8 c.σ.mem (fflushSpE g.sp).toNat
      (sdData_val (BitVec.ofNat 64 consoleStdout)),
    ⟨σ1, i1, c.steps + 1⟩,
    { step := hs1
      good := hG1
      tick := hi1
      mem := hmem1
      expected := rfl
      obs := hobs1 }⟩

theorem fflushEe08Step_persist (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (m : Mem) (hc : FflushAtEe08 g c)
    (hs : FflushEe08Step g c vm m c1) : FflushPersist g c1 :=
  fflushPersist_store g c c1 hc.toFflushPersist hs.good hs.tick hs.obs

theorem fflushEe08Step_mem (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (m : Mem) (hc : FflushAtEe08 g c)
    (hs : FflushEe08Step g c vm m c1) : c1.σ.mem = fflushPrefixM g := by
  rw [hs.mem, hs.expected, hc.mem]
  rfl

theorem fflushEe08Step_pc (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (m : Mem) (hs : FflushEe08Step g c vm m c1) :
    c1.σ.regs.get? Register.PC = some 0x8000ee0c#64 := by
  have h := obs_store_pc hs.obs
  rwa [show BitVec.addInt (0x8000ee08#64) 4 = 0x8000ee0c#64 from by decide] at h

theorem fflushEe08Step_a0 (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (m : Mem) (hc : FflushAtEe08 g c)
    (hs : FflushEe08Step g c vm m c1) :
    gprGet c1.σ 10 = some (BitVec.ofNat 64 consoleReent) :=
  obs_store_other' hs.obs Register.x10 (by decide) hc.a0

theorem fflushEe08Step_a1 (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (m : Mem) (hc : FflushAtEe08 g c)
    (hs : FflushEe08Step g c vm m c1) :
    gprGet c1.σ 11 = some (BitVec.ofNat 64 consoleStdout) :=
  obs_store_other' hs.obs Register.x11 (by decide) hc.a1

theorem fflushEe08Step_ra (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (m : Mem) (hc : FflushAtEe08 g c)
    (hs : FflushEe08Step g c vm m c1) :
    gprGet c1.σ 1 = some 0x8000ee50#64 :=
  obs_store_other' hs.obs Register.x1 (by decide) hc.ra

theorem fflushEe08Step_sp (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (m : Mem) (hc : FflushAtEe08 g c)
    (hs : FflushEe08Step g c vm m c1) :
    gprGet c1.σ 2 = some (fflushSpE g.sp) :=
  obs_store_other' hs.obs Register.x2 (by decide) hc.sp

theorem fflushEe08Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe08 g c) :
    ∃ c', Steps c c' ∧ FflushAtJal g c' := by
  obtain ⟨vm, m, c1, hs⟩ := fflushEe08Step_run g c hc
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushPersist := fflushEe08Step_persist g c c1 vm m hc hs
      mem := fflushEe08Step_mem g c c1 vm m hc hs
      pc := fflushEe08Step_pc g c c1 vm m hs
      a0 := fflushEe08Step_a0 g c c1 vm m hc hs
      a1 := fflushEe08Step_a1 g c c1 vm m hc hs
      ra := fflushEe08Step_ra g c c1 vm m hc hs
      sp := fflushEe08Step_sp g c c1 vm m hc hs }⟩

theorem fflushEe08Arm (g : FflushG) :
    Triple (FflushAtEe08 g) (FflushAtJal g) := by
  exact fflushEe08Arm_run g

/-
theorem fflushEe04Arm1_run (g : FflushG) (c : Config)
    (hc : FflushAtEe04 g c) :
    ∃ c', Steps c c' ∧ FflushAtEe08 g c' := by
  obtain ⟨vm0, hmi0⟩ := hc.minstret
  have hcode0 : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_acquire
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe04_site c.σ c.tick c.steps (0x8000ee04#64) vm0
      (BitVec.ofNat 64 consoleReent) hc.good hc.pc hmi0 hc.a4 hcode0 rfl hc.tick
  have hpc1 : σ1.regs.get? Register.PC = some 0x8000ee08#64 := by
    have h := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000ee04#64) 4 = 0x8000ee08#64 from by decide] at h
  obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
  have ha0_1 : gprGet σ1 10 = some (BitVec.ofNat 64 consoleReent) := by
    have h := obs_gpr_rd 10 (by decide) (by decide)
      (BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x000#12)) hobs1
    rwa [show BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x000#12) =
      BitVec.ofNat 64 consoleReent from by decide] at h
  have ha1_1 := obs_gpr_other hobs1 11 (by decide) (by decide) (by decide)
    (BitVec.ofNat 64 consoleStdout) hc.a1
  have hra1 := obs_gpr_other hobs1 1 (by decide) (by decide) (by decide)
    (0x8000ee50#64) hc.ra
  have hsp1 := obs_gpr_other hobs1 2 (by decide) (by decide) (by decide)
    (fflushSpE g.sp) hc.sp
  have hgp1 := obs_gpr_other hobs1 3 (by decide) (by decide) (by decide)
    wrGpVal hc.gp
  have hs0_1 := obs_gpr_other hobs1 8 (by decide) (by decide) (by decide)
    g.s0 hc.s0
  have hsregs1 : GHolds σ1 (sKeepL g.sv) := by
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
    exact ⟨
      obs_alu_other' hobs1 Register.x9 (by decide) k1,
      obs_alu_other' hobs1 Register.x18 (by decide) k2,
      obs_alu_other' hobs1 Register.x19 (by decide) k3,
      obs_alu_other' hobs1 Register.x20 (by decide) k4,
      obs_alu_other' hobs1 Register.x21 (by decide) k5,
      obs_alu_other' hobs1 Register.x22 (by decide) k6,
      obs_alu_other' hobs1 Register.x23 (by decide) k7,
      obs_alu_other' hobs1 Register.x24 (by decide) k8,
      obs_alu_other' hobs1 Register.x25 (by decide) k9,
      obs_alu_other' hobs1 Register.x26 (by decide) k10,
      obs_alu_other' hobs1 Register.x27 (by decide) k11,
      trivial⟩
  have hpw1 := obs_alu_other' hobs1 Register.htif_payload_writes
    (by decide) hc.pw
  obtain ⟨thv, hth0⟩ := hc.th
  have hth1 := obs_alu_other' hobs1 Register.htif_tohost (by decide) hth0
  exact ⟨⟨σ1, i1, c.steps + 1⟩, Steps.head hs1 (Steps.refl _),
    { ok := hc.ok
      good := hG1
      tick := hi1
      mem := hmem1.trans hc.mem
      pc := hpc1
      minstret := ⟨vm1, hmi1⟩
      a0 := ha0_1
      a1 := ha1_1
      ra := hra1
      sp := hsp1
      gp := hgp1
      s0 := hs0_1
      sregs := hsregs1
      out := hobs1.2.trans hc.out
      pw := hpw1
      th := ⟨thv, hth1⟩ }⟩

theorem fflushEe04Arm1 (g : FflushG) :
    Triple (FflushAtEe04 g) (FflushAtEe08 g) := by
  exact fflushEe04Arm1_run g

theorem fflushEe08Arm (g : FflushG) :
    Triple (FflushAtEe08 g) (FflushAtJal g) := by
  intro c hc
  obtain ⟨vm1, hmi1⟩ := hc.minstret
  have hcode1 : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_acquire
  have hrange := fflush_store0_range g.sp hc.ok.stack
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    fflushEe08_site c.σ c.tick c.steps (0x8000ee08#64) vm1
      (fflushSpE g.sp) (BitVec.ofNat 64 consoleStdout)
      hc.good hc.pc hmi1 hc.sp hc.a1 hcode1 rfl
      (by simpa using hrange.1)
      (by simpa using hrange.2.1)
      (by simpa using hrange.2.2.1)
      (by simpa using hrange.2.2.2) hc.tick
  have hsregs2 : GHolds σ2 (sKeepL g.sv) := by
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
    exact ⟨
      obs_store_other' hobs2 Register.x9 (by decide) k1,
      obs_store_other' hobs2 Register.x18 (by decide) k2,
      obs_store_other' hobs2 Register.x19 (by decide) k3,
      obs_store_other' hobs2 Register.x20 (by decide) k4,
      obs_store_other' hobs2 Register.x21 (by decide) k5,
      obs_store_other' hobs2 Register.x22 (by decide) k6,
      obs_store_other' hobs2 Register.x23 (by decide) k7,
      obs_store_other' hobs2 Register.x24 (by decide) k8,
      obs_store_other' hobs2 Register.x25 (by decide) k9,
      obs_store_other' hobs2 Register.x26 (by decide) k10,
      obs_store_other' hobs2 Register.x27 (by decide) k11,
      trivial⟩
  have hpw2 := obs_store_other' hobs2 Register.htif_payload_writes
    (by decide) hc.pw
  obtain ⟨thv, hth0⟩ := hc.th
  have hth2 := obs_store_other' hobs2 Register.htif_tohost (by decide) hth0
  refine ⟨⟨σ2, i2, c.steps + 1⟩,
    Steps.head hs2 (Steps.refl _), ?_⟩
  exact
    { ok := hc.ok
      good := hG2
      tick := hi2
      mem := by
        rw [hmem2]
        change writeMap8 c.σ.mem (fflushSpE g.sp).toNat
          (sdData_val (BitVec.ofNat 64 consoleStdout)) = fflushPrefixM g
        rw [hc.mem]
        rfl
      pc := by
        have h := obs_store_pc hobs2
        rwa [show BitVec.addInt (0x8000ee08#64) 4 = 0x8000ee0c#64 from by decide]
          at h
      minstret := obs_store_minstret hobs2
      a0 := obs_gpr_store hobs2 10 (by decide) (by decide)
        (BitVec.ofNat 64 consoleReent) hc.a0
      a1 := obs_gpr_store hobs2 11 (by decide) (by decide)
        (BitVec.ofNat 64 consoleStdout) hc.a1
      ra := obs_gpr_store hobs2 1 (by decide) (by decide) (0x8000ee50#64) hc.ra
      sp := obs_gpr_store hobs2 2 (by decide) (by decide) (fflushSpE g.sp) hc.sp
      gp := obs_gpr_store hobs2 3 (by decide) (by decide) wrGpVal hc.gp
      s0 := obs_gpr_store hobs2 8 (by decide) (by decide) g.s0 hc.s0
      sregs := hsregs2
      out := hobs2.2.trans hc.out
      pw := hpw2
      th := ⟨thv, hth2⟩ }

theorem fflushEe04Arm (g : FflushG) :
    Triple (FflushAtEe04 g) (FflushAtJal g) :=
  Triple.seq (fflushEe04Arm1 g) (fflushEe08Arm g)
-/

/-
theorem fflushEe04Arm1_run' (g : FflushG) (c : Config)
    (hc : FflushAtEe04 g c) :
    ∃ c', Steps c c' ∧ FflushAtEe08 g c' := by
  obtain ⟨vm0, hmi0⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_acquire
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe04_site c.σ c.tick c.steps (0x8000ee04#64) vm0
      (BitVec.ofNat 64 consoleReent) hc.good hc.pc hmi0 hc.a4 hcode rfl hc.tick
  let c1 : Config := ⟨σ1, i1, c.steps + 1⟩
  have hp1 : FflushPersist g c1 :=
    fflushPersist_alu10 g c c1 hc.toFflushPersist hG1 hi1 hobs1
  have ha0 : gprGet σ1 10 = some (BitVec.ofNat 64 consoleReent) := by
    have h := obs_gpr_rd 10 (by decide) (by decide)
      (BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x000#12)) hobs1
    rwa [show BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x000#12) =
      BitVec.ofNat 64 consoleReent from by decide] at h
  exact ⟨c1, Steps.head hs1 (Steps.refl _),
    { toFflushPersist := hp1
      mem := hmem1.trans hc.mem
      pc := by
        have h := obs_alu_pc hobs1
        rwa [show BitVec.addInt (0x8000ee04#64) 4 = 0x8000ee08#64 from by decide]
          at h
      a0 := ha0
      a1 := obs_gpr_other hobs1 11 (by decide) (by decide) (by decide)
        (BitVec.ofNat 64 consoleStdout) hc.a1
      ra := obs_gpr_other hobs1 1 (by decide) (by decide) (by decide)
        (0x8000ee50#64) hc.ra
      sp := obs_gpr_other hobs1 2 (by decide) (by decide) (by decide)
        (fflushSpE g.sp) hc.sp }⟩

theorem fflushEe04Arm1' (g : FflushG) :
    Triple (FflushAtEe04 g) (FflushAtEe08 g) := by
  exact fflushEe04Arm1_run' g
-/

theorem fflushEe04Arm1_run (g : FflushG) (c : Config)
    (hc : FflushAtEe04 g c) :
    ∃ c', Steps c c' ∧ FflushAtEe08 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe04Step_run g c hc
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushPersist := fflushEe04Step_persist g c c1 vm hc hs
      mem := fflushEe04Step_mem g c c1 vm hc hs
      pc := fflushEe04Step_pc g c c1 vm hs
      a0 := fflushEe04Step_a0 g c c1 vm hs
      a1 := fflushEe04Step_a1 g c c1 vm hc hs
      ra := fflushEe04Step_ra g c c1 vm hc hs
      sp := fflushEe04Step_sp g c c1 vm hc hs }⟩

theorem fflushEe04Arm1 (g : FflushG) :
    Triple (FflushAtEe04 g) (FflushAtEe08 g) := by
  exact fflushEe04Arm1_run g

theorem fflushEe04Arm (g : FflushG) :
    Triple (FflushAtEe04 g) (FflushAtJal g) :=
  Triple.seq (fflushEe04Arm1 g) (fflushEe08Arm g)

theorem fflushSflushJalArm (g : FflushG) :
    Triple (FflushAtJal g)
      (fun c => PCAt 0x8000eb70#64 c ∧ SflushFnPre (fflushSG g) c) := by
  intro c hA
  obtain ⟨vm1, hmi1⟩ := hA.minstret
  have hcF : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hA.mem]
    exact hA.ok.codeF_prefix
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee0c hcF
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000ee0c#64) vm1 (0xd65ff0ef#32)
      (0x1ffd64#21) (regidx.Regidx 0x01#5) Register.x1
      (BitVec.addInt (0x8000ee0c#64) 4)
      (0xef#8) (0xf0#8) (0x5f#8) (0xd6#8)
      hA.good hA.pc hmi1 hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_d65ff0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000ee0c#64) 4)) hA.tick
  refine ⟨⟨σ2, i2, c.steps + 1⟩, Steps.head hstep (Steps.refl _), ?_, ?_⟩
  · show σ2.regs.get? Register.PC = some 0x8000eb70#64
    rw [obs_jal_pc_env hobs]
    rw [show (0x8000ee0c#64 + sign_extend (m := 64) (0x1ffd64#21) : BitVec 64)
      = 0x8000eb70#64 from by decide]
  · have hra := obs_jal_rd_env hobs (by decide) (by decide) (by decide)
        (by decide) (by decide)
    have hra' : gprGet σ2 1 = some 0x8000ee10#64 := by
      rwa [show BitVec.addInt (0x8000ee0c#64) 4 = 0x8000ee10#64 from by decide]
        at hra
    have hok : SflushGOk (fflushSG g) :=
      { stack := hA.ok.stack.nested
        ra_align := by
          show (0x8000ee10#64).toNat % 4 = 0
          decide
        console := hA.ok.consolePrefix
        codeF := hA.ok.codeSflush
        codeW := hA.ok.codeWrite
        codeR := hA.ok.codeWriteR
        codeS := hA.ok.codeSwrite }
    exact
      { ok := hok
        good := hG2
        tick := hi2
        mem := hmem2.trans hA.mem
        minstret := obs_jal_minstret_env hobs
        a0 := obs_jal_other_env hobs Register.x10 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a0
        a1 := obs_jal_other_env hobs Register.x11 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a1
        ra := hra'
        sp := obs_jal_other_env hobs Register.x2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.sp
        gp := obs_jal_other_env hobs Register.x3 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.gp
        s0 := obs_jal_other_env hobs Register.x8 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.s0
        sregs := by
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hA.sregs
          exact ⟨
            obs_jal_other_env hobs Register.x9 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k1,
            obs_jal_other_env hobs Register.x18 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k2,
            obs_jal_other_env hobs Register.x19 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k3,
            obs_jal_other_env hobs Register.x20 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k4,
            obs_jal_other_env hobs Register.x21 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k5,
            obs_jal_other_env hobs Register.x22 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k6,
            obs_jal_other_env hobs Register.x23 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k7,
            obs_jal_other_env hobs Register.x24 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k8,
            obs_jal_other_env hobs Register.x25 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k9,
            obs_jal_other_env hobs Register.x26 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k10,
            obs_jal_other_env hobs Register.x27 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k11,
            trivial⟩
        out := hobs.2.trans ((sailOutput_sigmaPost_jal c.σ (0x8000ee0c#64) vm1
          (0x1ffd64#21) Register.x1 (BitVec.addInt (0x8000ee0c#64) 4)).trans hA.out)
        pw := obs_jal_other_env hobs Register.htif_payload_writes (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) hA.pw
        th := by
          obtain ⟨v, hv⟩ := hA.th
          exact ⟨v, obs_jal_other_env hobs Register.htif_tohost (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) hv⟩ }

theorem fflushSflushArm (g : FflushG) :
    Triple (FflushAtJal g)
      (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c) := by
  intro c hc
  obtain ⟨c1, hs1, h1⟩ := fflushSflushJalArm g c hc
  obtain ⟨c2, hs2, h2⟩ := (sflush_summary (fflushSG g)).run c1 h1
  exact ⟨c2, Steps.trans hs1 hs2, hc.ok, h2⟩

structure FflushAfterBase (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushAfterSflushM g
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (0#64)
  ra : gprGet c.σ 1 = some 0x8000ee10#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 [g.ch]
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

structure FflushAtEe10 (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee10#64

structure FflushAtEe14 (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee14#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)

structure FflushAtEe18 (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee18#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a5 : gprGet c.σ 15 = some (0#64)

structure FflushAtEe1c (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee1c#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a5 : gprGet c.σ 15 = some (0#64)
  a4 : gprGet c.σ 14 = some (0#64)

structure FflushAtEe20 (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee20#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a5 : gprGet c.σ 15 = some (0#64)
  a4 : gprGet c.σ 14 = some (0#64)

structure FflushAtEe24 (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee24#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a5 : gprGet c.σ 15 = some (0#64)

structure FflushAtEe28 (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee28#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a4 : gprGet c.σ 14 = some 0x200a#64

structure FflushAtEe2c (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee2c#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a4 : gprGet c.σ 14 = some (0#64)

structure FflushAtEe5c (g : FflushG) (c : Config) extends FflushAfterBase g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee5c#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)

structure FflushAtEe60 (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushReleaseM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee60#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (0#64)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  ra : gprGet c.σ 1 = some 0x8000ee10#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 [g.ch]
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

theorem fflushAtEe10_of_sflush (g : FflushG) (c : Config)
    (h : FflushGOk g ∧ SflushFnPost (fflushSG g) c) : FflushAtEe10 g c :=
  { ok := h.1
    good := h.2.good
    tick := h.2.tick
    mem := h.2.mem
    minstret := h.2.minstret
    a0 := h.2.a0
    ra := h.2.ra
    sp := h.2.sp
    gp := h.2.gp
    s0 := h.2.s0
    sregs := h.2.sregs
    out := h.2.out
    pw := h.2.pw
    th := h.2.th
    pc := h.2.pc }

theorem fflushAfterBase_alu11 (g : FflushG) (c c' : Config)
    {pc vm v : BitVec 64}
    (hp : FflushAfterBase g c) (hG : GoodState c'.σ) (hi : c'.tick < 2)
    (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ
      (sigmaPost_alu c.σ pc vm Register.x11 v)) : FflushAfterBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok
      good := hG
      tick := hi
      mem := hmem.trans hp.mem
      minstret := obs_alu_minstret hobs
      a0 := obs_alu_other' hobs Register.x10 (by decide) hp.a0
      ra := obs_alu_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_alu_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_alu_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_alu_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨
        obs_alu_other' hobs Register.x9 (by decide) k1,
        obs_alu_other' hobs Register.x18 (by decide) k2,
        obs_alu_other' hobs Register.x19 (by decide) k3,
        obs_alu_other' hobs Register.x20 (by decide) k4,
        obs_alu_other' hobs Register.x21 (by decide) k5,
        obs_alu_other' hobs Register.x22 (by decide) k6,
        obs_alu_other' hobs Register.x23 (by decide) k7,
        obs_alu_other' hobs Register.x24 (by decide) k8,
        obs_alu_other' hobs Register.x25 (by decide) k9,
        obs_alu_other' hobs Register.x26 (by decide) k10,
        obs_alu_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_alu_other' hobs Register.htif_payload_writes (by decide) hp.pw
      th := ⟨thv, obs_alu_other' hobs Register.htif_tohost (by decide) hth⟩ }

structure FflushEe10Step (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = BitVec.ofNat 64 consoleStdout
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee10#64) vm Register.x11 loaded)

theorem fflushEe10Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe10 g c) :
    ∃ vm loaded c1, FflushEe10Step g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  have hrange := fflush_store0_range g.sp hc.ok.stack
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe10_ld_site c.σ c.tick c.steps (0x8000ee10#64) vm
      (fflushSpE g.sp) hc.good hc.pc hmi hc.sp hcode rfl
      (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
        using hrange.1)
      (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
        using hrange.2.1)
      (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
        using (show (fflushSpE g.sp).toNat + 8 ≤ tohostAddr ∨
          tohostAddr + 8 ≤ (fflushSpE g.sp).toNat from by
            right
            omega))
      (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
        using hrange.2.2.2) hc.tick
  let loaded := sign_extend (m := 64)
    (bytesT8 c.σ.mem
      ((fflushSpE g.sp) + sign_extend (m := 64) (0x000#12)).toNat :
        BitVec (8 * 8))
  have heq : loaded = BitVec.ofNat 64 consoleStdout := by
    unfold loaded
    have hp : LPins8 c.σ.mem (fflushSpE g.sp).toNat
        (flushBytes8 (BitVec.ofNat 64 consoleStdout)) := by
      rw [hc.mem]
      exact fflush_lpins8_of_pin (fflushAfter_slot0_pin g hc.ok)
    have hb := bytesT8_of_lpins8 hp
    have haddr : (fflushSpE g.sp + sign_extend (m := 64) (0x000#12)).toNat =
        (fflushSpE g.sp).toNat := by
      rw [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
      simp
    rw [haddr]
    rw [hb]
    decide
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

def fflushReleaseKeep (g : FflushG) : GRegs :=
  [(10, 0#64), (2, fflushSpE g.sp), (3, wrGpVal), (8, g.s0)] ++
    sKeepL g.sv

structure FflushAtRelease (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushReleaseM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee64#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  ra : gprGet c.σ 1 = some 0x8000ee10#64
  keep : GHolds c.σ (fflushReleaseKeep g)
  out : c.σ.sailOutput = pushBytes g.out0 [g.ch]
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

theorem fflushEe10Step_base (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hc : FflushAtEe10 g c)
    (hs : FflushEe10Step g c vm loaded c1) : FflushAfterBase g c1 :=
  fflushAfterBase_alu11 g c c1 hc.toFflushAfterBase hs.good hs.tick hs.mem hs.obs

theorem fflushEe10Step_pc (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hs : FflushEe10Step g c vm loaded c1) :
    c1.σ.regs.get? Register.PC = some 0x8000ee14#64 := by
  have h := obs_alu_pc hs.obs
  rwa [show BitVec.addInt (0x8000ee10#64) 4 = 0x8000ee14#64 from by decide] at h

theorem fflushEe10Step_a1 (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hs : FflushEe10Step g c vm loaded c1) :
    gprGet c1.σ 11 = some (BitVec.ofNat 64 consoleStdout) := by
  have h := obs_gpr_rd 11 (by decide) (by decide) loaded hs.obs
  rwa [hs.loaded_eq] at h

theorem fflushEe10Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe10 g c) :
    ∃ c', Steps c c' ∧ FflushAtEe14 g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEe10Step_run g c hc
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushAfterBase := fflushEe10Step_base g c c1 vm loaded hc hs
      pc := fflushEe10Step_pc g c c1 vm loaded hs
      a1 := fflushEe10Step_a1 g c c1 vm loaded hs }⟩

theorem fflushEe10Arm (g : FflushG) :
    Triple (FflushAtEe10 g) (FflushAtEe14 g) :=
  fflushEe10Arm_run g

theorem fflushPostToEe10 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe10 g) := by
  intro c hc
  exact ⟨c, Steps.refl c, fflushAtEe10_of_sflush g c hc⟩

theorem fflushEe14_mv_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee14#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee14 hmem
  exact stepObs_alu σ i u (0x8000ee14#64) vminstret (0x00050793#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5,
      regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (v10 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x07#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00050793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5)
      (regidx.Regidx 0x0f#5) v10
      (afterNextPC (afterPrelude σ) (0x8000ee14#64))
      (sigma3_alu σ (0x8000ee14#64) Register.x15
        (v10 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x10 _ v10
        (by rw [get?_afterNextPC σ (0x8000ee14#64) _ (by decide) (by decide)]
            exact hx10))
      (wX_bits_x15 _ (v10 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem fflushAfterBase_alu15 (g : FflushG) (c c' : Config)
    {pc vm v : BitVec 64} (hp : FflushAfterBase g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2) (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ
      (sigmaPost_alu c.σ pc vm Register.x15 v)) : FflushAfterBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok, good := hG, tick := hi, mem := hmem.trans hp.mem
      minstret := obs_alu_minstret hobs
      a0 := obs_alu_other' hobs Register.x10 (by decide) hp.a0
      ra := obs_alu_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_alu_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_alu_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_alu_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨obs_alu_other' hobs Register.x9 (by decide) k1,
        obs_alu_other' hobs Register.x18 (by decide) k2,
        obs_alu_other' hobs Register.x19 (by decide) k3,
        obs_alu_other' hobs Register.x20 (by decide) k4,
        obs_alu_other' hobs Register.x21 (by decide) k5,
        obs_alu_other' hobs Register.x22 (by decide) k6,
        obs_alu_other' hobs Register.x23 (by decide) k7,
        obs_alu_other' hobs Register.x24 (by decide) k8,
        obs_alu_other' hobs Register.x25 (by decide) k9,
        obs_alu_other' hobs Register.x26 (by decide) k10,
        obs_alu_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_alu_other' hobs Register.htif_payload_writes (by decide) hp.pw
      th := ⟨thv, obs_alu_other' hobs Register.htif_tohost (by decide) hth⟩ }

structure FflushEe14Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee14#64) vm Register.x15
      (0#64 + sign_extend (m := 64) (0x000#12)))

theorem fflushEe14Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe14 g c) : ∃ vm c1, FflushEe14Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe14_mv_site c.σ c.tick c.steps (0x8000ee14#64) vm (0#64)
      hc.good hc.pc hmi hc.a0 hcode rfl hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEe14Step_base (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hc : FflushAtEe14 g c)
    (hs : FflushEe14Step g c vm c1) : FflushAfterBase g c1 :=
  fflushAfterBase_alu15 g c c1 hc.toFflushAfterBase hs.good hs.tick hs.mem hs.obs

theorem fflushEe14Step_pc (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hs : FflushEe14Step g c vm c1) :
    c1.σ.regs.get? Register.PC = some 0x8000ee18#64 := by
  have h := obs_alu_pc hs.obs
  rwa [show BitVec.addInt (0x8000ee14#64) 4 = 0x8000ee18#64 from by decide] at h

theorem fflushEe14Step_a1 (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hc : FflushAtEe14 g c)
    (hs : FflushEe14Step g c vm c1) :
    gprGet c1.σ 11 = some (BitVec.ofNat 64 consoleStdout) :=
  obs_alu_other' hs.obs Register.x11 (by decide) hc.a1

theorem fflushEe14Step_a5 (g : FflushG) (c c1 : Config)
    (vm : BitVec 64) (hs : FflushEe14Step g c vm c1) :
    gprGet c1.σ 15 = some (0#64) := by
  have h := obs_gpr_rd 15 (by decide) (by decide)
    (0#64 + sign_extend (m := 64) (0x000#12)) hs.obs
  simpa using h

theorem fflushEe14Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe14 g c) : ∃ c', Steps c c' ∧ FflushAtEe18 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe14Step_run g c hc
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushAfterBase := fflushEe14Step_base g c c1 vm hc hs
      pc := fflushEe14Step_pc g c c1 vm hs
      a1 := fflushEe14Step_a1 g c c1 vm hc hs
      a5 := fflushEe14Step_a5 g c c1 vm hs }⟩

theorem fflushEe14Arm (g : FflushG) :
    Triple (FflushAtEe14 g) (FflushAtEe18 g) := fflushEe14Arm_run g

theorem fflushEe18_lw_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee18#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x0b0#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x0b0#12)).toNat + 4 ≤
      0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x0b0#12)).toNat + 4 ≤
        tohostAddr ∨ tohostAddr + 8 ≤
          (v11 + sign_extend (m := 64) (0x0b0#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x0b0#12)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64)
            (bytesT4 σ.mem
              (v11 + sign_extend (m := 64) (0x0b0#12)).toNat :
                BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee18 hmem
  exact stepObs_alu σ i u (0x8000ee18#64) vminstret (0x0b05a703#32)
    (instruction.LOAD (0x0b0#12, regidx.Regidx 0x0b#5,
      regidx.Regidx 0x0e#5, false, 4)) Register.x14
    (sign_extend (m := 64)
      (bytesT4 σ.mem (v11 + sign_extend (m := 64) (0x0b0#12)).toNat :
        BitVec (8 * 4)))
    (0x03#8) (0xa7#8) (0x05#8) (0x0b#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0b05a703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw_tot σ (0x8000ee18#64) (0x0b0#12)
      (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5)
      (sigma3_alu σ (0x8000ee18#64) Register.x14
        (sign_extend (m := 64)
          (bytesT4 σ.mem (v11 + sign_extend (m := 64) (0x0b0#12)).toNat :
            BitVec (8 * 4)))) v11 hG
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x8000ee18#64) _ (by decide) (by decide)]
            exact hx11))
      (wX_bits_x14 _
        (sign_extend (m := 64)
          (bytesT4 σ.mem (v11 + sign_extend (m := 64) (0x0b0#12)).toNat :
            BitVec (8 * 4)))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem fflushAfterBase_alu14 (g : FflushG) (c c' : Config)
    {pc vm v : BitVec 64} (hp : FflushAfterBase g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2) (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ
      (sigmaPost_alu c.σ pc vm Register.x14 v)) : FflushAfterBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok, good := hG, tick := hi, mem := hmem.trans hp.mem
      minstret := obs_alu_minstret hobs
      a0 := obs_alu_other' hobs Register.x10 (by decide) hp.a0
      ra := obs_alu_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_alu_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_alu_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_alu_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨obs_alu_other' hobs Register.x9 (by decide) k1,
        obs_alu_other' hobs Register.x18 (by decide) k2,
        obs_alu_other' hobs Register.x19 (by decide) k3,
        obs_alu_other' hobs Register.x20 (by decide) k4,
        obs_alu_other' hobs Register.x21 (by decide) k5,
        obs_alu_other' hobs Register.x22 (by decide) k6,
        obs_alu_other' hobs Register.x23 (by decide) k7,
        obs_alu_other' hobs Register.x24 (by decide) k8,
        obs_alu_other' hobs Register.x25 (by decide) k9,
        obs_alu_other' hobs Register.x26 (by decide) k10,
        obs_alu_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_alu_other' hobs Register.htif_payload_writes (by decide) hp.pw
      th := ⟨thv, obs_alu_other' hobs Register.htif_tohost (by decide) hth⟩ }

structure FflushEe18Step (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = 0#64
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee18#64) vm Register.x14 loaded)

theorem fflushEe18Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe18 g c) :
    ∃ vm loaded c1, FflushEe18Step g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  have hcns := sflushCallbackM_console (fflushSG g) (fflushSG_ok g hc.ok)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe18_lw_site c.σ c.tick c.steps (0x8000ee18#64) vm
      (BitVec.ofNat 64 consoleStdout) hc.good hc.pc hmi hc.a1 hcode rfl
      (by decide) (by decide) (by right; decide) (by decide) hc.tick
  let loaded := sign_extend (m := 64)
    (bytesT4 c.σ.mem
      (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x0b0#12)).toNat : BitVec (8 * 4))
  have heq : loaded = 0#64 := by
    unfold loaded
    have hp : LPins4 c.σ.mem (consoleStdout + 176)
        [0#8, 0#8, 0#8, 0#8] := by
      rw [hc.mem]
      exact fflush_lpins4_zero hcns.lockMode
    have hb := bytesT4_of_lpins4 hp
    have haddr : (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x0b0#12)).toNat = consoleStdout + 176 := by
      decide
    rw [haddr, hb]
    decide
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEe18Step_base (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hc : FflushAtEe18 g c)
    (hs : FflushEe18Step g c vm loaded c1) : FflushAfterBase g c1 :=
  fflushAfterBase_alu14 g c c1 hc.toFflushAfterBase hs.good hs.tick hs.mem hs.obs

theorem fflushEe18Step_pc (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hs : FflushEe18Step g c vm loaded c1) :
    c1.σ.regs.get? Register.PC = some 0x8000ee1c#64 := by
  have h := obs_alu_pc hs.obs
  rwa [show BitVec.addInt (0x8000ee18#64) 4 = 0x8000ee1c#64 from by decide] at h

theorem fflushEe18Step_a1 (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hc : FflushAtEe18 g c)
    (hs : FflushEe18Step g c vm loaded c1) :
    gprGet c1.σ 11 = some (BitVec.ofNat 64 consoleStdout) :=
  obs_alu_other' hs.obs Register.x11 (by decide) hc.a1

theorem fflushEe18Step_a5 (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hc : FflushAtEe18 g c)
    (hs : FflushEe18Step g c vm loaded c1) : gprGet c1.σ 15 = some (0#64) :=
  obs_alu_other' hs.obs Register.x15 (by decide) hc.a5

theorem fflushEe18Step_a4 (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hs : FflushEe18Step g c vm loaded c1) :
    gprGet c1.σ 14 = some (0#64) := by
  have h := obs_gpr_rd 14 (by decide) (by decide) loaded hs.obs
  rwa [hs.loaded_eq] at h

theorem fflushEe18Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe18 g c) : ∃ c', Steps c c' ∧ FflushAtEe1c g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEe18Step_run g c hc
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushAfterBase := fflushEe18Step_base g c c1 vm loaded hc hs
      pc := fflushEe18Step_pc g c c1 vm loaded hs
      a1 := fflushEe18Step_a1 g c c1 vm loaded hc hs
      a5 := fflushEe18Step_a5 g c c1 vm loaded hc hs
      a4 := fflushEe18Step_a4 g c c1 vm loaded hs }⟩

theorem fflushEe18Arm (g : FflushG) :
    Triple (FflushAtEe18 g) (FflushAtEe1c g) := fflushEe18Arm_run g

theorem fflushEe1c_andi_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee1c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (v14 &&& sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee1c hmem
  exact stepObs_alu σ i u (0x8000ee1c#64) vminstret (0x00177713#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0e#5,
      regidx.Regidx 0x0e#5, iop.ANDI)) Register.x14
    (v14 &&& sign_extend (m := 64) (0x001#12))
    (0x13#8) (0x77#8) (0x17#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00177713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_andi_char (0x001#12) (regidx.Regidx 0x0e#5)
      (regidx.Regidx 0x0e#5) v14
      (afterNextPC (afterPrelude σ) (0x8000ee1c#64))
      (sigma3_alu σ (0x8000ee1c#64) Register.x14
        (v14 &&& sign_extend (m := 64) (0x001#12)))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x8000ee1c#64) _ (by decide) (by decide)]
            exact hx14))
      (wX_bits_x14 _ (v14 &&& sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe1cStep (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee1c#64) vm Register.x14
      (0#64 &&& sign_extend (m := 64) (0x001#12)))

theorem fflushEe1cStep_run (g : FflushG) (c : Config)
    (hc : FflushAtEe1c g c) : ∃ vm c1, FflushEe1cStep g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe1c_andi_site c.σ c.tick c.steps (0x8000ee1c#64) vm (0#64)
      hc.good hc.pc hmi hc.a4 hcode rfl hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEe1cArm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe1c g c) : ∃ c', Steps c c' ∧ FflushAtEe20 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe1cStep_run g c hc
  have hbase := fflushAfterBase_alu14 g c c1 hc.toFflushAfterBase
    hs.good hs.tick hs.mem hs.obs
  have hpc := obs_alu_pc hs.obs
  have ha4 := obs_gpr_rd 14 (by decide) (by decide)
    (0#64 &&& sign_extend (m := 64) (0x001#12)) hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushAfterBase := hbase
      pc := by
        rwa [show BitVec.addInt (0x8000ee1c#64) 4 = 0x8000ee20#64 from by decide]
          at hpc
      a1 := obs_alu_other' hs.obs Register.x11 (by decide) hc.a1
      a5 := obs_alu_other' hs.obs Register.x15 (by decide) hc.a5
      a4 := by simpa using ha4 }⟩

theorem fflushEe1cArm (g : FflushG) :
    Triple (FflushAtEe1c g) (FflushAtEe20 g) := fflushEe1cArm_run g

theorem fflushEe20_branch_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee20#64 : BitVec 64))
    (hv : (v14 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee20 hmem
  exact stepObs_branch_nottaken σ i u (0x8000ee20#64) vminstret (0x0010#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0x00071863#32)
    (0x63#8) (0x18#8) (0x07#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00071863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_nottaken (0x0010#13) (regidx.Regidx 0x0e#5)
      (regidx.Regidx 0x00#5) v14 (0#64)
      (afterNextPC (afterPrelude σ) (0x8000ee20#64))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x8000ee20#64) _ (by decide) (by decide)]
            exact hx14))
      (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem fflushAfterBase_branch_nt (g : FflushG) (c c' : Config)
    {pc vm : BitVec 64} (hp : FflushAfterBase g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2) (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ (sigmaPost_branch_nottaken c.σ pc vm)) :
    FflushAfterBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok, good := hG, tick := hi, mem := hmem.trans hp.mem
      minstret := obs_branch_nottaken_minstret hobs
      a0 := obs_branch_nottaken_other' hobs Register.x10 (by decide) hp.a0
      ra := obs_branch_nottaken_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_branch_nottaken_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_branch_nottaken_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_branch_nottaken_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨obs_branch_nottaken_other' hobs Register.x9 (by decide) k1,
        obs_branch_nottaken_other' hobs Register.x18 (by decide) k2,
        obs_branch_nottaken_other' hobs Register.x19 (by decide) k3,
        obs_branch_nottaken_other' hobs Register.x20 (by decide) k4,
        obs_branch_nottaken_other' hobs Register.x21 (by decide) k5,
        obs_branch_nottaken_other' hobs Register.x22 (by decide) k6,
        obs_branch_nottaken_other' hobs Register.x23 (by decide) k7,
        obs_branch_nottaken_other' hobs Register.x24 (by decide) k8,
        obs_branch_nottaken_other' hobs Register.x25 (by decide) k9,
        obs_branch_nottaken_other' hobs Register.x26 (by decide) k10,
        obs_branch_nottaken_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_branch_nottaken_other' hobs Register.htif_payload_writes
        (by decide) hp.pw
      th := ⟨thv, obs_branch_nottaken_other' hobs Register.htif_tohost
        (by decide) hth⟩ }

structure FflushEe20Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_branch_nottaken c.σ (0x8000ee20#64) vm)

theorem fflushEe20Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe20 g c) : ∃ vm c1, FflushEe20Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe20_branch_site c.σ c.tick c.steps (0x8000ee20#64) vm (0#64)
      hc.good hc.pc hmi hc.a4 hcode rfl (by decide) hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEe20Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe20 g c) : ∃ c', Steps c c' ∧ FflushAtEe24 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe20Step_run g c hc
  have hpc := obs_branch_nottaken_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushAfterBase := fflushAfterBase_branch_nt g c c1
        hc.toFflushAfterBase hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000ee20#64) 4 = 0x8000ee24#64 from by decide]
          at hpc
      a1 := obs_branch_nottaken_other' hs.obs Register.x11 (by decide) hc.a1
      a5 := obs_branch_nottaken_other' hs.obs Register.x15 (by decide) hc.a5 }⟩

theorem fflushEe20Arm (g : FflushG) :
    Triple (FflushAtEe20 g) (FflushAtEe24 g) := fflushEe20Arm_run g

theorem fflushEe24_lhu_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee24#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤
      0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤
        tohostAddr ∨ tohostAddr + 8 ≤
          (v11 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x010#12)).toNat % 2 = 0)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x010#12)).toNat]? = some 0x0a#8)
    (hb1 : σ.mem[(v11 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some 0x20#8)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (zero_extend (m := 64) ((0x20#8).append (0x0a#8)))) := by
  subst hpcv
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee24 hmem
  exact stepObs_alu σ i u (0x8000ee24#64) vminstret (0x0105d703#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0b#5,
      regidx.Regidx 0x0e#5, true, 2)) Register.x14
    (zero_extend (m := 64) ((0x20#8).append (0x0a#8)))
    (0x03#8) (0xd7#8) (0x05#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0105d703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lhu_gen σ (0x8000ee24#64) (0x010#12)
      (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5) v11 0x0a#8 0x20#8
      (sigma3_alu σ (0x8000ee24#64) Register.x14
        (zero_extend (m := 64) ((0x20#8).append (0x0a#8)))) hG
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x8000ee24#64) _ (by decide) (by decide)]
            exact hx11))
      (wX_bits_x14 _ (zero_extend (m := 64) ((0x20#8).append (0x0a#8))))
      hlo hhiram hhtif halign hb0 hb1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi

structure FflushEe24Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee24#64) vm Register.x14
      (zero_extend (m := 64) ((0x20#8).append (0x0a#8))))

theorem fflushEe24Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe24 g c) : ∃ vm c1, FflushEe24Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  have hcns := sflushCallbackM_console (fflushSG g) (fflushSG_ok g hc.ok)
  have hb0 : c.σ.mem[(BitVec.ofNat 64 consoleStdout +
      sign_extend (m := 64) (0x010#12)).toNat]? = some 0x0a#8 := by
    have h := hcns.flag0
    rw [hc.mem]
    simpa using h
  have hb1 : c.σ.mem[(BitVec.ofNat 64 consoleStdout +
      sign_extend (m := 64) (0x010#12)).toNat + 1]? = some 0x20#8 := by
    have h := hcns.flag1
    rw [hc.mem]
    simpa using h
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe24_lhu_site c.σ c.tick c.steps (0x8000ee24#64) vm
      (BitVec.ofNat 64 consoleStdout) hc.good hc.pc hmi hc.a1 hcode rfl
      (by decide) (by decide) (by right; decide) (by decide) hb0 hb1 hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEe24Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe24 g c) : ∃ c', Steps c c' ∧ FflushAtEe28 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe24Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have ha4 := obs_gpr_rd 14 (by decide) (by decide)
    (zero_extend (m := 64) ((0x20#8).append (0x0a#8))) hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushAfterBase := fflushAfterBase_alu14 g c c1 hc.toFflushAfterBase
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000ee24#64) 4 = 0x8000ee28#64 from by decide]
          at hpc
      a1 := obs_alu_other' hs.obs Register.x11 (by decide) hc.a1
      a4 := by
        rwa [show zero_extend (m := 64) ((0x20#8).append (0x0a#8)) =
          0x200a#64 from by decide] at ha4 }⟩

theorem fflushEe24Arm (g : FflushG) :
    Triple (FflushAtEe24 g) (FflushAtEe28 g) := fflushEe24Arm_run g

theorem fflushEe28_andi_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee28#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (v14 &&& sign_extend (m := 64) (0x200#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee28 hmem
  exact stepObs_alu σ i u (0x8000ee28#64) vminstret (0x20077713#32)
    (instruction.ITYPE (0x200#12, regidx.Regidx 0x0e#5,
      regidx.Regidx 0x0e#5, iop.ANDI)) Register.x14
    (v14 &&& sign_extend (m := 64) (0x200#12))
    (0x13#8) (0x77#8) (0x07#8) (0x20#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_20077713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_andi_char (0x200#12) (regidx.Regidx 0x0e#5)
      (regidx.Regidx 0x0e#5) v14
      (afterNextPC (afterPrelude σ) (0x8000ee28#64))
      (sigma3_alu σ (0x8000ee28#64) Register.x14
        (v14 &&& sign_extend (m := 64) (0x200#12)))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x8000ee28#64) _ (by decide) (by decide)]
            exact hx14))
      (wX_bits_x14 _ (v14 &&& sign_extend (m := 64) (0x200#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe28Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee28#64) vm Register.x14
      (0x200a#64 &&& sign_extend (m := 64) (0x200#12)))

theorem fflushEe28Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe28 g c) : ∃ vm c1, FflushEe28Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe28_andi_site c.σ c.tick c.steps (0x8000ee28#64) vm 0x200a#64
      hc.good hc.pc hmi hc.a4 hcode rfl hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEe28Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe28 g c) : ∃ c', Steps c c' ∧ FflushAtEe2c g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe28Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have ha4 := obs_gpr_rd 14 (by decide) (by decide)
    (0x200a#64 &&& sign_extend (m := 64) (0x200#12)) hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushAfterBase := fflushAfterBase_alu14 g c c1 hc.toFflushAfterBase
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000ee28#64) 4 = 0x8000ee2c#64 from by decide]
          at hpc
      a1 := obs_alu_other' hs.obs Register.x11 (by decide) hc.a1
      a4 := by
        rwa [show 0x200a#64 &&& sign_extend (m := 64) (0x200#12) = 0#64
          from by decide] at ha4 }⟩

theorem fflushEe28Arm (g : FflushG) :
    Triple (FflushAtEe28 g) (FflushAtEe2c g) := fflushEe28Arm_run g

theorem fflushEe2c_branch_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee2c#64 : BitVec 64))
    (hv : (v14 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_branch_taken σ pc vminstret (0x0030#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee2c hmem
  exact stepObs_branch_taken σ i u (0x8000ee2c#64) vminstret (0x0030#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02070863#32)
    (0x63#8) (0x08#8) (0x07#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02070863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_taken (0x0030#13) (regidx.Regidx 0x0e#5)
      (regidx.Regidx 0x00#5) v14 (0#64) (0x8000ee2c#64) initMisa
      (afterNextPC (afterPrelude σ) (0x8000ee2c#64))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x8000ee2c#64) _ (by decide) (by decide)]
            exact hx14)) (rX_bits_zero _)
      (by rw [get?_afterNextPC σ (0x8000ee2c#64) _ (by decide) (by decide)]
          exact hpc)
      (by rw [get?_afterNextPC σ (0x8000ee2c#64) _ (by decide) (by decide)]
          exact hG.misa)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem fflushAfterBase_branch_t (g : FflushG) (c c' : Config)
    {pc vm : BitVec 64} {imm : BitVec 13} (hp : FflushAfterBase g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2) (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ (sigmaPost_branch_taken c.σ pc vm imm)) :
    FflushAfterBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok, good := hG, tick := hi, mem := hmem.trans hp.mem
      minstret := obs_branch_taken_minstret hobs
      a0 := obs_branch_taken_other' hobs Register.x10 (by decide) hp.a0
      ra := obs_branch_taken_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_branch_taken_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_branch_taken_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_branch_taken_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨obs_branch_taken_other' hobs Register.x9 (by decide) k1,
        obs_branch_taken_other' hobs Register.x18 (by decide) k2,
        obs_branch_taken_other' hobs Register.x19 (by decide) k3,
        obs_branch_taken_other' hobs Register.x20 (by decide) k4,
        obs_branch_taken_other' hobs Register.x21 (by decide) k5,
        obs_branch_taken_other' hobs Register.x22 (by decide) k6,
        obs_branch_taken_other' hobs Register.x23 (by decide) k7,
        obs_branch_taken_other' hobs Register.x24 (by decide) k8,
        obs_branch_taken_other' hobs Register.x25 (by decide) k9,
        obs_branch_taken_other' hobs Register.x26 (by decide) k10,
        obs_branch_taken_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_branch_taken_other' hobs Register.htif_payload_writes
        (by decide) hp.pw
      th := ⟨thv, obs_branch_taken_other' hobs Register.htif_tohost
        (by decide) hth⟩ }

structure FflushEe2cStep (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_branch_taken c.σ (0x8000ee2c#64) vm (0x0030#13))

theorem fflushEe2cArm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe2c g c) : ∃ c', Steps c c' ∧ FflushAtEe5c g c' := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe2c_branch_site c.σ c.tick c.steps (0x8000ee2c#64) vm (0#64)
      hc.good hc.pc hmi hc.a4 hcode rfl (by decide) hc.tick
  let c1 : Config := ⟨σ1, i1, c.steps + 1⟩
  have hpc := obs_branch_taken_pc hobs1
  exact ⟨c1, Steps.head hs1 (Steps.refl _),
    { toFflushAfterBase := fflushAfterBase_branch_t g c c1 hc.toFflushAfterBase
        hG1 hi1 hmem1 hobs1
      pc := by
        rwa [show 0x8000ee2c#64 + sign_extend (m := 64) (0x0030#13) =
          0x8000ee5c#64 from by decide] at hpc
      a1 := obs_branch_taken_other' hobs1 Register.x11 (by decide) hc.a1 }⟩

theorem fflushEe2cArm (g : FflushG) :
    Triple (FflushAtEe2c g) (FflushAtEe5c g) := fflushEe2cArm_run g

theorem fflushEe5c_store_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee5c#64 : BitVec 64))
    (halo : 0x80000000 ≤ vsp.toNat)
    (hahiram : vsp.toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ vsp.toNat)
    (haalign : vsp.toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 σ.mem vsp.toNat (sdData_val v10) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap8 σ.mem vsp.toNat (sdData_val v10))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee5c hmem
  exact stepObs_store σ i u (0x8000ee5c#64) vminstret (0x00a13023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0a#5,
      regidx.Regidx 0x02#5, 8))
    (writeMap8 σ.mem vsp.toNat (sdData_val v10))
    (0x23#8) (0x30#8) (0xa1#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00a13023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by
      simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
        using exec_sd_val σ (0x8000ee5c#64) (0x000#12)
          (regidx.Regidx 0x0a#5) (regidx.Regidx 0x02#5) vsp v10 hG
          (rX_bits_x2 _ vsp (by
            rw [get?_afterNextPC σ (0x8000ee5c#64) _ (by decide) (by decide)]
            exact hx2))
          (rX_bits_x10 _ v10 (by
            rw [get?_afterNextPC σ (0x8000ee5c#64) _ (by decide) (by decide)]
            exact hx10))
          (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
            using halo)
          (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
            using hahiram)
          (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
            using hahiwin)
          (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
            using haalign))
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe5cStep (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = fflushReleaseM g
  obs : ReadsLikePost c1.σ
    (sigmaPost_store c.σ (0x8000ee5c#64) vm (fflushReleaseM g))

theorem fflushEe5cStep_run (g : FflushG) (c : Config)
    (hc : FflushAtEe5c g c) : ∃ vm c1, FflushEe5cStep g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_after
  have hrange := fflush_store0_range g.sp hc.ok.stack
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe5c_store_site c.σ c.tick c.steps (0x8000ee5c#64) vm
      (fflushSpE g.sp) (0#64) hc.good hc.pc hmi hc.sp hc.a0 hcode rfl
      hrange.1 hrange.2.1 hrange.2.2.1 hrange.2.2.2 hc.tick
  have hm : writeMap8 c.σ.mem (fflushSpE g.sp).toNat (sdData_val (0#64)) =
      fflushReleaseM g := by rw [hc.mem]; rfl
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1.trans hm, by rwa [hm] at hobs1⟩⟩

theorem fflushEe5cArm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe5c g c) : ∃ c', Steps c c' ∧ FflushAtEe60 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe5cStep_run g c hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  have hpc := obs_store_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { ok := hc.ok, good := hs.good, tick := hs.tick, mem := hs.mem
      pc := by
        rwa [show BitVec.addInt (0x8000ee5c#64) 4 = 0x8000ee60#64 from by decide]
          at hpc
      minstret := obs_store_minstret hs.obs
      a0 := obs_store_other' hs.obs Register.x10 (by decide) hc.a0
      a1 := obs_store_other' hs.obs Register.x11 (by decide) hc.a1
      ra := obs_store_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_store_other' hs.obs Register.x2 (by decide) hc.sp
      gp := obs_store_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_store_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨obs_store_other' hs.obs Register.x9 (by decide) k1,
        obs_store_other' hs.obs Register.x18 (by decide) k2,
        obs_store_other' hs.obs Register.x19 (by decide) k3,
        obs_store_other' hs.obs Register.x20 (by decide) k4,
        obs_store_other' hs.obs Register.x21 (by decide) k5,
        obs_store_other' hs.obs Register.x22 (by decide) k6,
        obs_store_other' hs.obs Register.x23 (by decide) k7,
        obs_store_other' hs.obs Register.x24 (by decide) k8,
        obs_store_other' hs.obs Register.x25 (by decide) k9,
        obs_store_other' hs.obs Register.x26 (by decide) k10,
        obs_store_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_store_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_store_other' hs.obs Register.htif_tohost (by decide) hth⟩ }⟩

theorem fflushEe5cArm (g : FflushG) :
    Triple (FflushAtEe5c g) (FflushAtEe60 g) := fflushEe5cArm_run g

theorem fflushEe60_ld_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee60#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x0a0#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x0a0#12)).toNat + 8 ≤
      0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x0a0#12)).toNat + 8 ≤
        tohostAddr ∨ tohostAddr + 8 ≤
          (v11 + sign_extend (m := 64) (0x0a0#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x0a0#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
            (bytesT8 σ.mem
              (v11 + sign_extend (m := 64) (0x0a0#12)).toNat :
                BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee60 hmem
  exact stepObs_alu σ i u (0x8000ee60#64) vminstret (0x0a05b503#32)
    (instruction.LOAD (0x0a0#12, regidx.Regidx 0x0b#5,
      regidx.Regidx 0x0a#5, false, 8)) Register.x10
    (sign_extend (m := 64)
      (bytesT8 σ.mem (v11 + sign_extend (m := 64) (0x0a0#12)).toNat :
        BitVec (8 * 8)))
    (0x03#8) (0xb5#8) (0x05#8) (0x0a#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0a05b503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_tot σ (0x8000ee60#64) (0x0a0#12)
      (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x8000ee60#64) Register.x10
        (sign_extend (m := 64)
          (bytesT8 σ.mem (v11 + sign_extend (m := 64) (0x0a0#12)).toNat :
            BitVec (8 * 8)))) v11 hG
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x8000ee60#64) _ (by decide) (by decide)]
            exact hx11))
      (wX_bits_x10 _
        (sign_extend (m := 64)
          (bytesT8 σ.mem (v11 + sign_extend (m := 64) (0x0a0#12)).toNat :
            BitVec (8 * 8)))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe60Step (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = 0#64
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee60#64) vm Register.x10 loaded)

theorem fflushEe60Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe60 g c) :
    ∃ vm loaded c1, FflushEe60Step g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_release
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe60_ld_site c.σ c.tick c.steps (0x8000ee60#64) vm
      (BitVec.ofNat 64 consoleStdout) hc.good hc.pc hmi hc.a1 hcode rfl
      (by decide) (by decide) (by right; decide) (by decide) hc.tick
  let loaded := sign_extend (m := 64)
    (bytesT8 c.σ.mem
      (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x0a0#12)).toNat : BitVec (8 * 8))
  have heq : loaded = 0#64 := by
    unfold loaded
    have hcns := sflushCallbackM_console (fflushSG g) (fflushSG_ok g hc.ok)
    have hlock : read64 c.σ.mem (consoleStdout + 160) = some 0 := by
      rw [hc.mem]
      unfold fflushReleaseM
      rw [read64_writeMap8_disjoint]
      · exact hcns.lock
      · left
        have hs := hc.ok.stack.nested.console
        omega
    have hp := fflush_lpins8_zero hlock
    have hb := bytesT8_of_lpins8 hp
    have haddr : (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x0a0#12)).toNat = consoleStdout + 160 := by decide
    rw [haddr, hb]
    decide
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEe60Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe60 g c) : ∃ c', Steps c c' ∧ FflushAtRelease g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEe60Step_run g c hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  have hpc := obs_alu_pc hs.obs
  have ha0 := obs_gpr_rd 10 (by decide) (by decide) loaded hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { ok := hc.ok, good := hs.good, tick := hs.tick
      mem := hs.mem.trans hc.mem
      pc := by
        rwa [show BitVec.addInt (0x8000ee60#64) 4 = 0x8000ee64#64 from by decide]
          at hpc
      minstret := obs_alu_minstret hs.obs
      ra := obs_alu_other' hs.obs Register.x1 (by decide) hc.ra
      keep := ⟨by rwa [hs.loaded_eq] at ha0,
        obs_alu_other' hs.obs Register.x2 (by decide) hc.sp,
        obs_alu_other' hs.obs Register.x3 (by decide) hc.gp,
        obs_alu_other' hs.obs Register.x8 (by decide) hc.s0,
        obs_alu_other' hs.obs Register.x9 (by decide) k1,
        obs_alu_other' hs.obs Register.x18 (by decide) k2,
        obs_alu_other' hs.obs Register.x19 (by decide) k3,
        obs_alu_other' hs.obs Register.x20 (by decide) k4,
        obs_alu_other' hs.obs Register.x21 (by decide) k5,
        obs_alu_other' hs.obs Register.x22 (by decide) k6,
        obs_alu_other' hs.obs Register.x23 (by decide) k7,
        obs_alu_other' hs.obs Register.x24 (by decide) k8,
        obs_alu_other' hs.obs Register.x25 (by decide) k9,
        obs_alu_other' hs.obs Register.x26 (by decide) k10,
        obs_alu_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_alu_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_alu_other' hs.obs Register.htif_tohost (by decide) hth⟩ }⟩

theorem fflushEe60Arm (g : FflushG) :
    Triple (FflushAtEe60 g) (FflushAtRelease g) := fflushEe60Arm_run g

theorem fflushReleaseJalArm (g : FflushG) :
    Triple (FflushAtRelease g)
      (fun c => PCAt 0x80006ff8#64 c ∧
        RetStubPre 0x8000ee68#64 (fflushReleaseKeep g)
          (fflushReleaseM g) (pushBytes g.out0 [g.ch]) (0#4) c) := by
  intro c hA
  obtain ⟨vm1, hmi1⟩ := hA.minstret
  have hcF : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hA.mem]
    exact hA.ok.codeF_release
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee64 hcF
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000ee64#64) vm1 (0x994f80ef#32)
      (0x1f8194#21) (regidx.Regidx 0x01#5) Register.x1
      (BitVec.addInt (0x8000ee64#64) 4)
      (0xef#8) (0x80#8) (0x4f#8) (0x99#8)
      hA.good hA.pc hmi1 hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_994f80ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000ee64#64) 4)) hA.tick
  refine ⟨⟨σ2, i2, c.steps + 1⟩, Steps.head hstep (Steps.refl _), ?_, ?_⟩
  · show σ2.regs.get? Register.PC = some 0x80006ff8#64
    rw [obs_jal_pc_env hobs]
    rw [show (0x8000ee64#64 + sign_extend (m := 64) (0x1f8194#21) : BitVec 64)
      = 0x80006ff8#64 from by decide]
  · have hra := obs_jal_rd_env hobs (by decide) (by decide) (by decide)
        (by decide) (by decide)
    have hra' : gprGet σ2 1 = some 0x8000ee68#64 := by
      rwa [show BitVec.addInt (0x8000ee64#64) 4 = 0x8000ee68#64 from by decide]
        at hra
    obtain ⟨ka0, ksp, kgp, ks0,
      k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hA.keep
    exact
      { good := hG2
        tick := hi2
        mem := hmem2.trans hA.mem
        minstret := obs_jal_minstret_env hobs
        ra := hra'
        keep := ⟨
          obs_jal_other_env hobs Register.x10 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) ka0,
          obs_jal_other_env hobs Register.x2 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) ksp,
          obs_jal_other_env hobs Register.x3 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) kgp,
          obs_jal_other_env hobs Register.x8 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) ks0,
          obs_jal_other_env hobs Register.x9 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k1,
          obs_jal_other_env hobs Register.x18 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k2,
          obs_jal_other_env hobs Register.x19 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k3,
          obs_jal_other_env hobs Register.x20 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k4,
          obs_jal_other_env hobs Register.x21 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k5,
          obs_jal_other_env hobs Register.x22 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k6,
          obs_jal_other_env hobs Register.x23 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k7,
          obs_jal_other_env hobs Register.x24 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k8,
          obs_jal_other_env hobs Register.x25 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k9,
          obs_jal_other_env hobs Register.x26 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k10,
          obs_jal_other_env hobs Register.x27 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) k11,
          trivial⟩
        out := hobs.2.trans ((sailOutput_sigmaPost_jal c.σ (0x8000ee64#64) vm1
          (0x1f8194#21) Register.x1 (BitVec.addInt (0x8000ee64#64) 4)).trans hA.out)
        pw := obs_jal_other_env hobs Register.htif_payload_writes (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) hA.pw
        th := by
          obtain ⟨v, hv⟩ := hA.th
          exact ⟨v, obs_jal_other_env hobs Register.htif_tohost (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) hv⟩ }

theorem fflushReleaseArm (g : FflushG) :
    Triple (FflushAtRelease g)
      (RetStubPost 0x8000ee68#64 (fflushReleaseKeep g)
        (fflushReleaseM g) (pushBytes g.out0 [g.ch]) (0#4)) := by
  intro c hc
  obtain ⟨c1, hs1, h1⟩ := fflushReleaseJalArm g c hc
  have T := lockRelease_summary 0x8000ee68#64 (fflushReleaseKeep g)
    (fflushReleaseM g) (pushBytes g.out0 [g.ch]) (0#4)
    (by
      change FrameOK [10, 2, 3, 8, 9, 18, 19, 20, 21, 22, 23,
        24, 25, 26, 27] retarget_lock_release_recursiveX6ff8Seg
      decide)
    hc.ok.codeRelease
    (by apply BitVec.eq_of_toNat_eq; decide) (by decide)
  obtain ⟨c2, hs2, h2⟩ := T.run c1 h1
  exact ⟨c2, Steps.trans hs1 hs2, h2⟩

structure FflushEpiloguePersist (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushReleaseM g
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 [g.ch]
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

structure FflushAtEe68 (g : FflushG) (c : Config)
    extends FflushEpiloguePersist g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee68#64
  a0 : gprGet c.σ 10 = some (0#64)
  ra : gprGet c.σ 1 = some 0x8000ee68#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe6c (g : FflushG) (c : Config)
    extends FflushEpiloguePersist g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee6c#64
  a0 : gprGet c.σ 10 = some (0#64)
  a5 : gprGet c.σ 15 = some (0#64)
  ra : gprGet c.σ 1 = some 0x8000ee68#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe70 (g : FflushG) (c : Config)
    extends FflushEpiloguePersist g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee70#64
  a0 : gprGet c.σ 10 = some (0#64)
  a5 : gprGet c.σ 15 = some (0#64)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe74 (g : FflushG) (c : Config)
    extends FflushEpiloguePersist g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee74#64
  a0 : gprGet c.σ 10 = some (0#64)
  a5 : gprGet c.σ 15 = some (0#64)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe78 (g : FflushG) (c : Config)
    extends FflushEpiloguePersist g c where
  pc : c.σ.regs.get? Register.PC = some 0x8000ee78#64
  a0 : gprGet c.σ 10 = some (0#64)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some g.sp

structure FflushFnPost (g : FflushG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushReleaseM g
  pc : c.σ.regs.get? Register.PC = some g.ra
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (0#64)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some g.sp
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 [g.ch]
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

theorem fflushAtEe68_of_release (g : FflushG) (c : Config)
    (h : FflushGOk g ∧ RetStubPost 0x8000ee68#64 (fflushReleaseKeep g)
      (fflushReleaseM g) (pushBytes g.out0 [g.ch]) (0#4) c) :
    FflushAtEe68 g c := by
  obtain ⟨ka0, ksp, kgp, ks0,
    k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := h.2.keep
  exact
    { ok := h.1
      good := h.2.good
      tick := h.2.tick
      mem := h.2.mem
      minstret := h.2.minstret
      gp := kgp
      s0 := ks0
      sregs := ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, trivial⟩
      out := h.2.out
      pw := h.2.pw
      th := h.2.th
      pc := h.2.pc
      a0 := ka0
      ra := h.2.ra
      sp := ksp }

theorem fflushReleaseArm_ok (g : FflushG) :
    Triple (FflushAtRelease g)
      (fun c => FflushGOk g ∧
        RetStubPost 0x8000ee68#64 (fflushReleaseKeep g)
          (fflushReleaseM g) (pushBytes g.out0 [g.ch]) (0#4) c) := by
  intro c hc
  obtain ⟨c1, hs, h1⟩ := fflushReleaseArm g c hc
  exact ⟨c1, hs, hc.ok, h1⟩

theorem fflushReleaseToEe68 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧
      RetStubPost 0x8000ee68#64 (fflushReleaseKeep g)
        (fflushReleaseM g) (pushBytes g.out0 [g.ch]) (0#4) c)
      (FflushAtEe68 g) := by
  intro c hc
  exact ⟨c, Steps.refl c, fflushAtEe68_of_release g c hc⟩

theorem fflushRelease_slot0_pin (g : FflushG) :
    Pin8 (fflushReleaseM g) (fflushSpE g.sp).toNat (0#64) := by
  unfold fflushReleaseM
  exact Pin8_writeMap8 _ _ _

theorem fflushRelease_slot0_read64 (g : FflushG) :
    read64 (fflushReleaseM g) (fflushSpE g.sp).toNat = some 0 := by
  unfold fflushReleaseM
  rw [read64_writeMap8]
  exact congrArg some (sdData_toNat (0#64))

/-
theorem fflushRelease_slot24_pin (g : FflushG) (hg : FflushGOk g) :
    Pin8 (fflushReleaseM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
  have hp0 : Pin8
      (writeMap8 g.m0
        (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat
        (sdData_val g.ra))
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra :=
    Pin8_writeMap8 _ _ _
  have hpA : Pin8 (fflushAcquireM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
    unfold fflushAcquireM
    apply Pin8_frame _ (Pin8_frame _ hp0)
    · intro k hk0 hk1
      rw [getElem_writeMap8_disjoint]
      rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
        fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
      rw [show sign_extend (m := 64) (0x008#12) = 8#64 by decide,
        fflush_slot_toNat g.sp hg.stack 8 (by decide)]
      omega
    · intro k hk0 hk1
      rw [getElem_writeMap8_disjoint]
      rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
        fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
      rw [fflush_spE_toNat g.sp hg.stack]
      omega
  have hpP : Pin8 (fflushPrefixM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
    unfold fflushPrefixM
    apply Pin8_frame _ hpA
    intro k hk0 hk1
    rw [getElem_writeMap8_disjoint]
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
    rw [fflush_spE_toNat g.sp hg.stack]
    omega
  have hpS : Pin8 (fflushAfterSflushM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
    apply Pin8_frame _ hpP
    intro k hk0 hk1
    apply sflushCallbackM_outer_entry (fflushSG g) (fflushSG_ok g hg) k
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
    exact hk0
  unfold fflushReleaseM
  apply Pin8_frame _ hpS
  intro k hk0 hk1
  rw [getElem_writeMap8_disjoint]
  rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
    fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
  rw [fflush_spE_toNat g.sp hg.stack]
  omega
-/

/-
theorem fflushAcquire_slot24_pin (g : FflushG) (hg : FflushGOk g) :
    Pin8 (fflushAcquireM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
  let mra := writeMap8 g.m0
    (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat
    (sdData_val g.ra)
  have hp : Pin8 mra
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
    exact Pin8_writeMap8 _ _ _
  have hp8 : Pin8
      (writeMap8 mra
        (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
        (sdData_val (BitVec.ofNat 64 consoleReent)))
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
    apply Pin8_frame _ hp
    intro k hk0 hk1
    rw [getElem_writeMap8_disjoint]
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
    rw [show sign_extend (m := 64) (0x008#12) = 8#64 by decide,
      fflush_slot_toNat g.sp hg.stack 8 (by decide)]
    omega
  unfold fflushAcquireM
  change Pin8
    (writeMap8
      (writeMap8 mra
        (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
        (sdData_val (BitVec.ofNat 64 consoleReent)))
      (fflushSpE g.sp).toNat (sdData_val (BitVec.ofNat 64 consoleStdout)))
    (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra
  apply Pin8_frame _ hp8
  intro k hk0 hk1
  rw [getElem_writeMap8_disjoint]
  rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
    fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
  rw [fflush_spE_toNat g.sp hg.stack]
  omega

theorem fflushPrefix_slot24_pin (g : FflushG) (hg : FflushGOk g) :
    Pin8 (fflushPrefixM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
  unfold fflushPrefixM
  apply Pin8_frame _ (fflushAcquire_slot24_pin g hg)
  intro k hk0 hk1
  rw [getElem_writeMap8_disjoint]
  rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
    fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
  rw [fflush_spE_toNat g.sp hg.stack]
  omega

theorem fflushAfter_slot24_pin (g : FflushG) (hg : FflushGOk g) :
    Pin8 (fflushAfterSflushM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
  apply Pin8_frame _ (fflushPrefix_slot24_pin g hg)
  intro k hk0 hk1
  apply sflushCallbackM_outer_entry (fflushSG g) (fflushSG_ok g hg) k
  rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
    fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
  exact hk0

theorem fflushRelease_slot24_pin' (g : FflushG) (hg : FflushGOk g) :
    Pin8 (fflushReleaseM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.ra := by
  unfold fflushReleaseM
  apply Pin8_frame _ (fflushAfter_slot24_pin g hg)
  intro k hk0 hk1
  rw [getElem_writeMap8_disjoint]
  rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
    fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk0
  rw [fflush_spE_toNat g.sp hg.stack]
  omega
-/

theorem fflushAcquire_slot24_read64 (g : FflushG) (hg : FflushGOk g) :
    read64 (fflushAcquireM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
      some g.ra.toNat := by
  unfold fflushAcquireM
  rw [read64_writeMap8_disjoint, read64_writeMap8_disjoint, read64_writeMap8]
  · exact congrArg some (sdData_toNat g.ra)
  · right
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    rw [show sign_extend (m := 64) (0x008#12) = 8#64 by decide,
      fflush_slot_toNat g.sp hg.stack 8 (by decide)]
    omega
  · right
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    rw [fflush_spE_toNat g.sp hg.stack]
    omega

theorem fflushPrefix_slot24_read64 (g : FflushG) (hg : FflushGOk g) :
    read64 (fflushPrefixM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
      some g.ra.toNat := by
  unfold fflushPrefixM
  rw [read64_writeMap8_disjoint]
  · exact fflushAcquire_slot24_read64 g hg
  · right
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    rw [fflush_spE_toNat g.sp hg.stack]
    omega

theorem fflushAfter_slot24_read64 (g : FflushG) (hg : FflushGOk g) :
    read64 (fflushAfterSflushM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
      some g.ra.toNat := by
  let a := (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat
  have hag : AgreeP (fun k => a ≤ k ∧ k < a + 8)
      (fflushAfterSflushM g) (fflushPrefixM g) := by
    intro k hk
    exact sflushCallbackM_outer_entry (fflushSG g) (fflushSG_ok g hg) k (by
      unfold a at hk
      rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
        fflush_slot_toNat g.sp hg.stack 24 (by decide)] at hk
      change (fflushSpE g.sp).toNat ≤ k
      rw [fflush_spE_toNat g.sp hg.stack]
      omega)
  change read64 (fflushAfterSflushM g) a = some g.ra.toNat
  rw [read64_agreeP hag (by intro k hk; exact ⟨by omega, by omega⟩)]
  exact fflushPrefix_slot24_read64 g hg

theorem fflushRelease_slot24_read64 (g : FflushG) (hg : FflushGOk g) :
    read64 (fflushReleaseM g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
      some g.ra.toNat := by
  unfold fflushReleaseM
  rw [read64_writeMap8_disjoint]
  · exact fflushAfter_slot24_read64 g hg
  · right
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    rw [fflush_spE_toNat g.sp hg.stack]
    omega

theorem fflush_load64_eq_of_read64 {m : Mem} {a : Nat} {v : BitVec 64}
    (h : read64 m a = some v.toNat) :
    (sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8)) : BitVec 64) = v :=
  load64_eq_of_read64 h

theorem fflushEe68_ld_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hsp : σ.regs.get? Register.x2 = some vsp)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee68#64 : BitVec 64))
    (hlo : 0x80000000 ≤ vsp.toNat)
    (hhiram : vsp.toNat + 8 ≤ 0x100000000)
    (hhtif : vsp.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vsp.toNat)
    (halign : vsp.toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) (bytesT8 σ.mem vsp.toNat : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee68 hmem
  exact stepObs_alu σ i u (0x8000ee68#64) vminstret (0x00013783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x02#5,
      regidx.Regidx 0x0f#5, false, 8)) Register.x15
    (sign_extend (m := 64) (bytesT8 σ.mem vsp.toNat : BitVec (8 * 8)))
    (0x83#8) (0x37#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00013783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by
      have hzero : sign_extend (m := 64) (0x000#12) = 0#64 := by decide
      have hz :
          (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
        rw [hzero, BitVec.add_zero]
      simpa only [hz]
        using exec_ld_tot σ (0x8000ee68#64) (0x000#12)
          (regidx.Regidx 0x02#5) (regidx.Regidx 0x0f#5)
          (sigma3_alu σ (0x8000ee68#64) Register.x15
            (sign_extend (m := 64)
              (bytesT8 σ.mem
                (vsp + sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8))))
          vsp hG
          (rX_bits_x2 _ vsp (by
            rw [get?_afterNextPC σ (0x8000ee68#64) _ (by decide) (by decide)]
            exact hsp))
          (wX_bits_x15 _
            (sign_extend (m := 64)
              (bytesT8 σ.mem
                (vsp + sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8))))
          (by simpa only [hz] using hlo)
          (by simpa only [hz] using hhiram)
          (by simpa only [hz] using hhtif)
          (by simpa only [hz] using halign))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe68Step (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = 0#64
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee68#64) vm Register.x15 loaded)

theorem fflushEe68Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe68 g c) :
    ∃ vm loaded c1, FflushEe68Step g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_release
  have hrange := fflush_store0_range g.sp hc.ok.stack
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe68_ld_site c.σ c.tick c.steps (0x8000ee68#64) vm
      (fflushSpE g.sp) hc.good hc.pc hmi hc.sp hcode rfl
      hrange.1 hrange.2.1 (by right; omega) hrange.2.2.2 hc.tick
  let loaded := sign_extend (m := 64)
    (bytesT8 c.σ.mem (fflushSpE g.sp).toNat : BitVec (8 * 8))
  have heq : loaded = 0#64 := by
    unfold loaded
    apply fflush_load64_eq_of_read64
    rw [hc.mem]
    exact fflushRelease_slot0_read64 g
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEe68Step_persist (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hc : FflushAtEe68 g c)
    (hs : FflushEe68Step g c vm loaded c1) : FflushEpiloguePersist g c1 := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  exact
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      mem := hs.mem.trans hc.mem
      minstret := obs_alu_minstret hs.obs
      gp := obs_alu_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_alu_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_alu_other' hs.obs Register.x9 (by decide) k1,
        obs_alu_other' hs.obs Register.x18 (by decide) k2,
        obs_alu_other' hs.obs Register.x19 (by decide) k3,
        obs_alu_other' hs.obs Register.x20 (by decide) k4,
        obs_alu_other' hs.obs Register.x21 (by decide) k5,
        obs_alu_other' hs.obs Register.x22 (by decide) k6,
        obs_alu_other' hs.obs Register.x23 (by decide) k7,
        obs_alu_other' hs.obs Register.x24 (by decide) k8,
        obs_alu_other' hs.obs Register.x25 (by decide) k9,
        obs_alu_other' hs.obs Register.x26 (by decide) k10,
        obs_alu_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_alu_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_alu_other' hs.obs Register.htif_tohost (by decide) hth⟩ }

theorem fflushEe68Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe68 g c) : ∃ c', Steps c c' ∧ FflushAtEe6c g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEe68Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have ha5 := obs_gpr_rd 15 (by decide) (by decide) loaded hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushEpiloguePersist := fflushEe68Step_persist g c c1 vm loaded hc hs
      pc := by
        rwa [show BitVec.addInt (0x8000ee68#64) 4 = 0x8000ee6c#64 from by decide]
          at hpc
      a0 := obs_alu_other' hs.obs Register.x10 (by decide) hc.a0
      a5 := by rwa [hs.loaded_eq] at ha5
      ra := obs_alu_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_alu_other' hs.obs Register.x2 (by decide) hc.sp }⟩

theorem fflushEe68Arm (g : FflushG) :
    Triple (FflushAtEe68 g) (FflushAtEe6c g) := fflushEe68Arm_run g

theorem fflushEe6c_ld_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hsp : σ.regs.get? Register.x2 = some vsp)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee6c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x018#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤
      0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x018#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x1
          (sign_extend (m := 64)
            (bytesT8 σ.mem
              (vsp + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee6c hmem
  exact stepObs_alu σ i u (0x8000ee6c#64) vminstret (0x01813083#32)
    (instruction.LOAD (0x018#12, regidx.Regidx 0x02#5,
      regidx.Regidx 0x01#5, false, 8)) Register.x1
    (sign_extend (m := 64)
      (bytesT8 σ.mem
        (vsp + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8)))
    (0x83#8) (0x30#8) (0x81#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01813083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_tot σ (0x8000ee6c#64) (0x018#12)
      (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x8000ee6c#64) Register.x1
        (sign_extend (m := 64)
          (bytesT8 σ.mem
            (vsp + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8))))
      vsp hG
      (rX_bits_x2 _ vsp (by
        rw [get?_afterNextPC σ (0x8000ee6c#64) _ (by decide) (by decide)]
        exact hsp))
      (wX_bits_x1 _
        (sign_extend (m := 64)
          (bytesT8 σ.mem
            (vsp + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8))))
      hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe6cStep (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = g.ra
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee6c#64) vm Register.x1 loaded)

theorem fflushEe6cStep_run (g : FflushG) (c : Config)
    (hc : FflushAtEe6c g c) :
    ∃ vm loaded c1, FflushEe6cStep g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_release
  obtain ⟨hlo0, hhi0, hhost0, halign0⟩ :=
    fflush_store0_range g.sp hc.ok.stack
  rw [fflush_spE_toNat g.sp hc.ok.stack] at hlo0 hhi0 hhost0 halign0
  have haddr :
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
        g.sp.toNat - 32 + 24 := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hc.ok.stack 24 (by decide)]
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe6c_ld_site c.σ c.tick c.steps (0x8000ee6c#64) vm
      (fflushSpE g.sp) hc.good hc.pc hmi hc.sp hcode rfl
      (by rw [haddr]; omega)
      (by
        rw [haddr]
        calc
          g.sp.toNat - 32 + 24 + 8 = g.sp.toNat - 32 + 32 := by omega
          _ = g.sp.toNat := Nat.sub_add_cancel hc.ok.stack.lo
          _ ≤ 0x100000000 := hc.ok.stack.hi)
      (by right; rw [haddr]; omega)
      (by rw [haddr]; omega) hc.tick
  let loaded := sign_extend (m := 64)
    (bytesT8 c.σ.mem
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat :
        BitVec (8 * 8))
  have heq : loaded = g.ra := by
    unfold loaded
    apply fflush_load64_eq_of_read64
    rw [hc.mem]
    exact fflushRelease_slot24_read64 g hc.ok
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEe6cStep_persist (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hc : FflushAtEe6c g c)
    (hs : FflushEe6cStep g c vm loaded c1) : FflushEpiloguePersist g c1 := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  exact
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      mem := hs.mem.trans hc.mem
      minstret := obs_alu_minstret hs.obs
      gp := obs_alu_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_alu_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_alu_other' hs.obs Register.x9 (by decide) k1,
        obs_alu_other' hs.obs Register.x18 (by decide) k2,
        obs_alu_other' hs.obs Register.x19 (by decide) k3,
        obs_alu_other' hs.obs Register.x20 (by decide) k4,
        obs_alu_other' hs.obs Register.x21 (by decide) k5,
        obs_alu_other' hs.obs Register.x22 (by decide) k6,
        obs_alu_other' hs.obs Register.x23 (by decide) k7,
        obs_alu_other' hs.obs Register.x24 (by decide) k8,
        obs_alu_other' hs.obs Register.x25 (by decide) k9,
        obs_alu_other' hs.obs Register.x26 (by decide) k10,
        obs_alu_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_alu_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_alu_other' hs.obs Register.htif_tohost (by decide) hth⟩ }

theorem fflushEe6cArm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe6c g c) : ∃ c', Steps c c' ∧ FflushAtEe70 g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEe6cStep_run g c hc
  have hpc := obs_alu_pc hs.obs
  have hra := obs_gpr_rd 1 (by decide) (by decide) loaded hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushEpiloguePersist := fflushEe6cStep_persist g c c1 vm loaded hc hs
      pc := by
        rwa [show BitVec.addInt (0x8000ee6c#64) 4 = 0x8000ee70#64 from by decide]
          at hpc
      a0 := obs_alu_other' hs.obs Register.x10 (by decide) hc.a0
      a5 := obs_alu_other' hs.obs Register.x15 (by decide) hc.a5
      ra := by rwa [hs.loaded_eq] at hra
      sp := obs_alu_other' hs.obs Register.x2 (by decide) hc.sp }⟩

theorem fflushEe6cArm (g : FflushG) :
    Triple (FflushAtEe6c g) (FflushAtEe70 g) := fflushEe6cArm_run g

theorem fflushEe70_mv_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee70#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (v15 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee70 hmem
  exact stepObs_alu σ i u (0x8000ee70#64) vminstret (0x00078513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0f#5,
      regidx.Regidx 0x0a#5, iop.ADDI)) Register.x10
    (v15 + sign_extend (m := 64) (0x000#12))
    (0x13#8) (0x85#8) (0x07#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00078513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0f#5)
      (regidx.Regidx 0x0a#5) v15
      (afterNextPC (afterPrelude σ) (0x8000ee70#64))
      (sigma3_alu σ (0x8000ee70#64) Register.x10
        (v15 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x15 _ v15 (by
        rw [get?_afterNextPC σ (0x8000ee70#64) _ (by decide) (by decide)]
        exact hx15))
      (wX_bits_x10 _ (v15 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe70Step (g : FflushG) (c : Config)
    (vm result : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  result_eq : result = 0#64
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee70#64) vm Register.x10 result)

theorem fflushEe70Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe70 g c) :
    ∃ vm result c1, FflushEe70Step g c vm result c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_release
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe70_mv_site c.σ c.tick c.steps (0x8000ee70#64) vm (0#64)
      hc.good hc.pc hmi hc.a5 hcode rfl hc.tick
  let result := (0#64) + sign_extend (m := 64) (0x000#12)
  exact ⟨vm, result, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, by decide, hobs1⟩⟩

theorem fflushEe70Step_persist (g : FflushG) (c c1 : Config)
    (vm result : BitVec 64) (hc : FflushAtEe70 g c)
    (hs : FflushEe70Step g c vm result c1) : FflushEpiloguePersist g c1 := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  exact
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      mem := hs.mem.trans hc.mem
      minstret := obs_alu_minstret hs.obs
      gp := obs_alu_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_alu_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_alu_other' hs.obs Register.x9 (by decide) k1,
        obs_alu_other' hs.obs Register.x18 (by decide) k2,
        obs_alu_other' hs.obs Register.x19 (by decide) k3,
        obs_alu_other' hs.obs Register.x20 (by decide) k4,
        obs_alu_other' hs.obs Register.x21 (by decide) k5,
        obs_alu_other' hs.obs Register.x22 (by decide) k6,
        obs_alu_other' hs.obs Register.x23 (by decide) k7,
        obs_alu_other' hs.obs Register.x24 (by decide) k8,
        obs_alu_other' hs.obs Register.x25 (by decide) k9,
        obs_alu_other' hs.obs Register.x26 (by decide) k10,
        obs_alu_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_alu_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_alu_other' hs.obs Register.htif_tohost (by decide) hth⟩ }

theorem fflushEe70Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe70 g c) : ∃ c', Steps c c' ∧ FflushAtEe74 g c' := by
  obtain ⟨vm, result, c1, hs⟩ := fflushEe70Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have ha0 := obs_gpr_rd 10 (by decide) (by decide) result hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushEpiloguePersist := fflushEe70Step_persist g c c1 vm result hc hs
      pc := by
        rwa [show BitVec.addInt (0x8000ee70#64) 4 = 0x8000ee74#64 from by decide]
          at hpc
      a0 := by rwa [hs.result_eq] at ha0
      a5 := obs_alu_other' hs.obs Register.x15 (by decide) hc.a5
      ra := obs_alu_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_alu_other' hs.obs Register.x2 (by decide) hc.sp }⟩

theorem fflushEe70Arm (g : FflushG) :
    Triple (FflushAtEe70 g) (FflushAtEe74 g) := fflushEe70Arm_run g

theorem fflushEe74_addi_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hsp : σ.regs.get? Register.x2 = some vsp)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee74#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2
          (vsp + sign_extend (m := 64) (0x020#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee74 hmem
  exact stepObs_alu σ i u (0x8000ee74#64) vminstret (0x02010113#32)
    (instruction.ITYPE (0x020#12, regidx.Regidx 0x02#5,
      regidx.Regidx 0x02#5, iop.ADDI)) Register.x2
    (vsp + sign_extend (m := 64) (0x020#12))
    (0x13#8) (0x01#8) (0x01#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x020#12) (regidx.Regidx 0x02#5)
      (regidx.Regidx 0x02#5) vsp
      (afterNextPC (afterPrelude σ) (0x8000ee74#64))
      (sigma3_alu σ (0x8000ee74#64) Register.x2
        (vsp + sign_extend (m := 64) (0x020#12)))
      (rX_bits_x2 _ vsp (by
        rw [get?_afterNextPC σ (0x8000ee74#64) _ (by decide) (by decide)]
        exact hsp))
      (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0x020#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe74Step (g : FflushG) (c : Config)
    (vm result : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  result_eq : result = g.sp
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee74#64) vm Register.x2 result)

theorem fflushEe74Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe74 g c) :
    ∃ vm result c1, FflushEe74Step g c vm result c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_release
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe74_addi_site c.σ c.tick c.steps (0x8000ee74#64) vm
      (fflushSpE g.sp) hc.good hc.pc hmi hc.sp hcode rfl hc.tick
  let result := fflushSpE g.sp + sign_extend (m := 64) (0x020#12)
  have heq : result = g.sp := by
    unfold result fflushSpE
    exact sp_dec32_restore g.sp
  exact ⟨vm, result, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEe74Step_persist (g : FflushG) (c c1 : Config)
    (vm result : BitVec 64) (hc : FflushAtEe74 g c)
    (hs : FflushEe74Step g c vm result c1) : FflushEpiloguePersist g c1 := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  exact
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      mem := hs.mem.trans hc.mem
      minstret := obs_alu_minstret hs.obs
      gp := obs_alu_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_alu_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_alu_other' hs.obs Register.x9 (by decide) k1,
        obs_alu_other' hs.obs Register.x18 (by decide) k2,
        obs_alu_other' hs.obs Register.x19 (by decide) k3,
        obs_alu_other' hs.obs Register.x20 (by decide) k4,
        obs_alu_other' hs.obs Register.x21 (by decide) k5,
        obs_alu_other' hs.obs Register.x22 (by decide) k6,
        obs_alu_other' hs.obs Register.x23 (by decide) k7,
        obs_alu_other' hs.obs Register.x24 (by decide) k8,
        obs_alu_other' hs.obs Register.x25 (by decide) k9,
        obs_alu_other' hs.obs Register.x26 (by decide) k10,
        obs_alu_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_alu_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_alu_other' hs.obs Register.htif_tohost (by decide) hth⟩ }

theorem fflushEe74Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe74 g c) : ∃ c', Steps c c' ∧ FflushAtEe78 g c' := by
  obtain ⟨vm, result, c1, hs⟩ := fflushEe74Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have hsp := obs_gpr_rd 2 (by decide) (by decide) result hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushEpiloguePersist := fflushEe74Step_persist g c c1 vm result hc hs
      pc := by
        rwa [show BitVec.addInt (0x8000ee74#64) 4 = 0x8000ee78#64 from by decide]
          at hpc
      a0 := obs_alu_other' hs.obs Register.x10 (by decide) hc.a0
      ra := obs_alu_other' hs.obs Register.x1 (by decide) hc.ra
      sp := by rwa [hs.result_eq] at hsp }⟩

theorem fflushEe74Arm (g : FflushG) :
    Triple (FflushAtEe74 g) (FflushAtEe78 g) := fflushEe74Arm_run g

theorem fflushEe78_jr_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hra : σ.regs.get? Register.x1 = some vra)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee78#64 : BitVec 64))
    (htgt : (BitVec.update
      (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (BitVec.update
            (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee78 hmem
  exact stepObs_jr σ i u (0x8000ee78#64) vminstret vra (0x00008067#32)
    (0x000#12) (regidx.Regidx 0x01#5)
    (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3
    (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (rX_bits_x1 _ vra (by
      rw [get?_afterNextPC σ (0x8000ee78#64) _ (by decide) (by decide)]
      exact hra))
    htgt hi

theorem fflushEe78Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe78 g c) : ∃ c', Steps c c' ∧ FflushFnPost g c' := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_release
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe78_jr_site c.σ c.tick c.steps (0x8000ee78#64) vm g.ra
      hc.good hc.pc hmi hc.ra hcode rfl
      (by rw [ret_tgt g.ra hc.ok.ra_align]; exact hc.ok.ra_align) hc.tick
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  have hpc := obs_jr_pc hobs1
  exact ⟨⟨σ1, i1, c.steps + 1⟩, Steps.head hs1 (Steps.refl _),
    { good := hG1
      tick := hi1
      mem := hmem1.trans hc.mem
      pc := by rwa [ret_tgt g.ra hc.ok.ra_align] at hpc
      minstret := obs_jr_minstret hobs1
      a0 := obs_jr_other' hobs1 Register.x10 (by decide) hc.a0
      ra := obs_jr_other' hobs1 Register.x1 (by decide) hc.ra
      sp := obs_jr_other' hobs1 Register.x2 (by decide) hc.sp
      gp := obs_jr_other' hobs1 Register.x3 (by decide) hc.gp
      s0 := obs_jr_other' hobs1 Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_jr_other' hobs1 Register.x9 (by decide) k1,
        obs_jr_other' hobs1 Register.x18 (by decide) k2,
        obs_jr_other' hobs1 Register.x19 (by decide) k3,
        obs_jr_other' hobs1 Register.x20 (by decide) k4,
        obs_jr_other' hobs1 Register.x21 (by decide) k5,
        obs_jr_other' hobs1 Register.x22 (by decide) k6,
        obs_jr_other' hobs1 Register.x23 (by decide) k7,
        obs_jr_other' hobs1 Register.x24 (by decide) k8,
        obs_jr_other' hobs1 Register.x25 (by decide) k9,
        obs_jr_other' hobs1 Register.x26 (by decide) k10,
        obs_jr_other' hobs1 Register.x27 (by decide) k11, trivial⟩
      out := hobs1.2.trans hc.out
      pw := obs_jr_other' hobs1 Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_jr_other' hobs1 Register.htif_tohost (by decide) hth⟩ }⟩

theorem fflushEe78Arm (g : FflushG) :
    Triple (FflushAtEe78 g) (FflushFnPost g) := fflushEe78Arm_run g

theorem fflushEpilogueArm (g : FflushG) :
    Triple (FflushAtEe68 g) (FflushFnPost g) :=
  Triple.seq (fflushEe68Arm g)
    (Triple.seq (fflushEe6cArm g)
      (Triple.seq (fflushEe70Arm g)
        (Triple.seq (fflushEe74Arm g) (fflushEe78Arm g))))

structure FflushAtEe50 (g : FflushG) (c : Config) extends FflushPersist g c where
  mem : c.σ.mem = fflushAcquireM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee50#64
  ra : gprGet c.σ 1 = some 0x8000ee50#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe54 (g : FflushG) (c : Config) extends FflushPersist g c where
  mem : c.σ.mem = fflushAcquireM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee54#64
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  ra : gprGet c.σ 1 = some 0x8000ee50#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe58 (g : FflushG) (c : Config) extends FflushPersist g c where
  mem : c.σ.mem = fflushAcquireM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee58#64
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  ra : gprGet c.σ 1 = some 0x8000ee50#64
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

theorem fflushAcquireArm_ok (g : FflushG) :
    Triple (FflushAtAcquire g)
      (fun c => FflushGOk g ∧
        RetStubPost 0x8000ee50#64 (fflushAcquireKeep g)
          (fflushAcquireM g) g.out0 (0#4) c) := by
  intro c hc
  obtain ⟨c1, hs, h1⟩ := fflushAcquireArm g c hc
  exact ⟨c1, hs, hc.ok, h1⟩

theorem fflushAtEe50_of_acquire (g : FflushG) (c : Config)
    (h : FflushGOk g ∧ RetStubPost 0x8000ee50#64 (fflushAcquireKeep g)
      (fflushAcquireM g) g.out0 (0#4) c) : FflushAtEe50 g c := by
  obtain ⟨ka0, ka1, ka4, ksp, kgp, ks0,
    k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := h.2.keep
  exact
    { ok := h.1
      good := h.2.good
      tick := h.2.tick
      minstret := h.2.minstret
      gp := kgp
      s0 := ks0
      sregs := ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, trivial⟩
      out := h.2.out
      pw := h.2.pw
      th := h.2.th
      mem := h.2.mem
      pc := h.2.pc
      ra := h.2.ra
      sp := ksp }

theorem fflushAcquireToEe50 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧
      RetStubPost 0x8000ee50#64 (fflushAcquireKeep g)
        (fflushAcquireM g) g.out0 (0#4) c) (FflushAtEe50 g) := by
  intro c hc
  exact ⟨c, Steps.refl c, fflushAtEe50_of_acquire g c hc⟩

theorem fflushEe50_ld_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hsp : σ.regs.get? Register.x2 = some vsp)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee50#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤
      0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64)
            (bytesT8 σ.mem
              (vsp + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee50 hmem
  exact stepObs_alu σ i u (0x8000ee50#64) vminstret (0x00813703#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x02#5,
      regidx.Regidx 0x0e#5, false, 8)) Register.x14
    (sign_extend (m := 64)
      (bytesT8 σ.mem
        (vsp + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8)))
    (0x03#8) (0x37#8) (0x81#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00813703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_tot σ (0x8000ee50#64) (0x008#12)
      (regidx.Regidx 0x02#5) (regidx.Regidx 0x0e#5)
      (sigma3_alu σ (0x8000ee50#64) Register.x14
        (sign_extend (m := 64)
          (bytesT8 σ.mem
            (vsp + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8))))
      vsp hG
      (rX_bits_x2 _ vsp (by
        rw [get?_afterNextPC σ (0x8000ee50#64) _ (by decide) (by decide)]
        exact hsp))
      (wX_bits_x14 _
        (sign_extend (m := 64)
          (bytesT8 σ.mem
            (vsp + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8))))
      hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe50Step (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = BitVec.ofNat 64 consoleReent
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee50#64) vm Register.x14 loaded)

theorem fflushEe50Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe50 g c) :
    ∃ vm loaded c1, FflushEe50Step g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_acquire
  obtain ⟨hlo0, hhi0, hhost0, halign0⟩ :=
    fflush_store0_range g.sp hc.ok.stack
  have haddr :
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat =
        g.sp.toNat - 32 + 8 := by
    rw [show sign_extend (m := 64) (0x008#12) = 8#64 by decide,
      fflush_slot_toNat g.sp hc.ok.stack 8 (by decide)]
  rw [fflush_spE_toNat g.sp hc.ok.stack] at hlo0 hhi0 hhost0 halign0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe50_ld_site c.σ c.tick c.steps (0x8000ee50#64) vm
      (fflushSpE g.sp) hc.good hc.pc hmi hc.sp hcode rfl
      (by rw [haddr]; clear hhi0 hhost0 halign0; omega)
      (by
        rw [haddr]
        clear hlo0 hhost0 halign0
        have hcancel := Nat.sub_add_cancel hc.ok.stack.lo
        have htop := hc.ok.stack.hi
        omega)
      (by right; rw [haddr]; clear hlo0 hhi0 halign0; omega)
      (by rw [haddr]; clear hlo0 hhi0 hhost0; omega) hc.tick
  let loaded := sign_extend (m := 64)
    (bytesT8 c.σ.mem
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat :
        BitVec (8 * 8))
  have heq : loaded = BitVec.ofNat 64 consoleReent := by
    unfold loaded
    have hp : LPins8 c.σ.mem
        (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
        (flushBytes8 (BitVec.ofNat 64 consoleReent)) := by
      rw [hc.mem]
      exact fflush_lpins8_of_pin (fflushAcquire_slot8_pin g hc.ok)
    rw [bytesT8_of_lpins8 hp]
    decide
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEe50Step_persist (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hc : FflushAtEe50 g c)
    (hs : FflushEe50Step g c vm loaded c1) : FflushPersist g c1 := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  exact
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      minstret := obs_alu_minstret hs.obs
      gp := obs_alu_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_alu_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_alu_other' hs.obs Register.x9 (by decide) k1,
        obs_alu_other' hs.obs Register.x18 (by decide) k2,
        obs_alu_other' hs.obs Register.x19 (by decide) k3,
        obs_alu_other' hs.obs Register.x20 (by decide) k4,
        obs_alu_other' hs.obs Register.x21 (by decide) k5,
        obs_alu_other' hs.obs Register.x22 (by decide) k6,
        obs_alu_other' hs.obs Register.x23 (by decide) k7,
        obs_alu_other' hs.obs Register.x24 (by decide) k8,
        obs_alu_other' hs.obs Register.x25 (by decide) k9,
        obs_alu_other' hs.obs Register.x26 (by decide) k10,
        obs_alu_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_alu_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_alu_other' hs.obs Register.htif_tohost (by decide) hth⟩ }

theorem fflushEe50Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe50 g c) : ∃ c', Steps c c' ∧ FflushAtEe54 g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEe50Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have ha4 := obs_gpr_rd 14 (by decide) (by decide) loaded hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushPersist := fflushEe50Step_persist g c c1 vm loaded hc hs
      mem := hs.mem.trans hc.mem
      pc := by
        rwa [show BitVec.addInt (0x8000ee50#64) 4 = 0x8000ee54#64 from by decide]
          at hpc
      a4 := by rwa [hs.loaded_eq] at ha4
      ra := obs_alu_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_alu_other' hs.obs Register.x2 (by decide) hc.sp }⟩

theorem fflushEe50Arm (g : FflushG) :
    Triple (FflushAtEe50 g) (FflushAtEe54 g) := fflushEe50Arm_run g

theorem fflushEe54_ld_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hsp : σ.regs.get? Register.x2 = some vsp)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee54#64 : BitVec 64))
    (hlo : 0x80000000 ≤ vsp.toNat)
    (hhiram : vsp.toNat + 8 ≤ 0x100000000)
    (hhtif : vsp.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vsp.toNat)
    (halign : vsp.toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (sign_extend (m := 64) (bytesT8 σ.mem vsp.toNat : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee54 hmem
  exact stepObs_alu σ i u (0x8000ee54#64) vminstret (0x00013583#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x02#5,
      regidx.Regidx 0x0b#5, false, 8)) Register.x11
    (sign_extend (m := 64) (bytesT8 σ.mem vsp.toNat : BitVec (8 * 8)))
    (0x83#8) (0x35#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00013583 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by
      have hzero : sign_extend (m := 64) (0x000#12) = 0#64 := by decide
      have hz :
          (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
        rw [hzero, BitVec.add_zero]
      simpa only [hz]
        using exec_ld_tot σ (0x8000ee54#64) (0x000#12)
          (regidx.Regidx 0x02#5) (regidx.Regidx 0x0b#5)
          (sigma3_alu σ (0x8000ee54#64) Register.x11
            (sign_extend (m := 64)
              (bytesT8 σ.mem
                (vsp + sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8))))
          vsp hG
          (rX_bits_x2 _ vsp (by
            rw [get?_afterNextPC σ (0x8000ee54#64) _ (by decide) (by decide)]
            exact hsp))
          (wX_bits_x11 _
            (sign_extend (m := 64)
              (bytesT8 σ.mem
                (vsp + sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8))))
          (by simpa only [hz] using hlo)
          (by simpa only [hz] using hhiram)
          (by simpa only [hz] using hhtif)
          (by simpa only [hz] using halign))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe54Step (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = BitVec.ofNat 64 consoleStdout
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee54#64) vm Register.x11 loaded)

theorem fflushEe54Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe54 g c) :
    ∃ vm loaded c1, FflushEe54Step g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_acquire
  obtain ⟨hlo, hhi, hhost, halign⟩ := fflush_store0_range g.sp hc.ok.stack
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe54_ld_site c.σ c.tick c.steps (0x8000ee54#64) vm
      (fflushSpE g.sp) hc.good hc.pc hmi hc.sp hcode rfl
      hlo hhi (by right; omega) halign hc.tick
  let loaded := sign_extend (m := 64)
    (bytesT8 c.σ.mem (fflushSpE g.sp).toNat : BitVec (8 * 8))
  have heq : loaded = BitVec.ofNat 64 consoleStdout := by
    unfold loaded
    have hp : LPins8 c.σ.mem (fflushSpE g.sp).toNat
        (flushBytes8 (BitVec.ofNat 64 consoleStdout)) := by
      rw [hc.mem]
      exact fflush_lpins8_of_pin (fflushAcquire_slot0_pin g)
    rw [bytesT8_of_lpins8 hp]
    decide
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEe54Step_persist (g : FflushG) (c c1 : Config)
    (vm loaded : BitVec 64) (hc : FflushAtEe54 g c)
    (hs : FflushEe54Step g c vm loaded c1) : FflushPersist g c1 := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  exact
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      minstret := obs_alu_minstret hs.obs
      gp := obs_alu_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_alu_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_alu_other' hs.obs Register.x9 (by decide) k1,
        obs_alu_other' hs.obs Register.x18 (by decide) k2,
        obs_alu_other' hs.obs Register.x19 (by decide) k3,
        obs_alu_other' hs.obs Register.x20 (by decide) k4,
        obs_alu_other' hs.obs Register.x21 (by decide) k5,
        obs_alu_other' hs.obs Register.x22 (by decide) k6,
        obs_alu_other' hs.obs Register.x23 (by decide) k7,
        obs_alu_other' hs.obs Register.x24 (by decide) k8,
        obs_alu_other' hs.obs Register.x25 (by decide) k9,
        obs_alu_other' hs.obs Register.x26 (by decide) k10,
        obs_alu_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_alu_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_alu_other' hs.obs Register.htif_tohost (by decide) hth⟩ }

theorem fflushEe54Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe54 g c) : ∃ c', Steps c c' ∧ FflushAtEe58 g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEe54Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have ha1 := obs_gpr_rd 11 (by decide) (by decide) loaded hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushPersist := fflushEe54Step_persist g c c1 vm loaded hc hs
      mem := hs.mem.trans hc.mem
      pc := by
        rwa [show BitVec.addInt (0x8000ee54#64) 4 = 0x8000ee58#64 from by decide]
          at hpc
      a4 := obs_alu_other' hs.obs Register.x14 (by decide) hc.a4
      a1 := by rwa [hs.loaded_eq] at ha1
      ra := obs_alu_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_alu_other' hs.obs Register.x2 (by decide) hc.sp }⟩

theorem fflushEe54Arm (g : FflushG) :
    Triple (FflushAtEe54 g) (FflushAtEe58 g) := fflushEe54Arm_run g

theorem fflushEe58_j_site (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code._fflush_rLoaded σ.mem)
    (hpcv : pc = (0x8000ee58#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (pc + sign_extend (m := 64) (0x1fffac#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee58 hmem
  exact stepObs_j σ i u (0x8000ee58#64) vminstret (0xfadff06f#32)
    (0x1fffac#21) (0x6f#8) (0xf0#8) (0xdf#8) (0xfa#8)
    hG hpc hminstret hb0 hb1 hb2 hb3
    (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fadff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide) hi

structure FflushEe58Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_jump_x0 c.σ (0x8000ee58#64) vm
      ((0x8000ee58#64) + sign_extend (m := 64) (0x1fffac#21)))

theorem fflushEe58Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe58 g c) : ∃ vm c1, FflushEe58Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hcode : Vsa.Sim.Code._fflush_rLoaded c.σ.mem := by
    rw [hc.mem]
    exact hc.ok.codeF_acquire
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe58_j_site c.σ c.tick c.steps (0x8000ee58#64) vm
      hc.good hc.pc hmi hcode rfl hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEe58Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe58 g c) : ∃ c', Steps c c' ∧ FflushAtEe04 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe58Step_run g c hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  have hpc := obs_jr_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      minstret := obs_jr_minstret hs.obs
      gp := obs_jr_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_jr_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_jr_other' hs.obs Register.x9 (by decide) k1,
        obs_jr_other' hs.obs Register.x18 (by decide) k2,
        obs_jr_other' hs.obs Register.x19 (by decide) k3,
        obs_jr_other' hs.obs Register.x20 (by decide) k4,
        obs_jr_other' hs.obs Register.x21 (by decide) k5,
        obs_jr_other' hs.obs Register.x22 (by decide) k6,
        obs_jr_other' hs.obs Register.x23 (by decide) k7,
        obs_jr_other' hs.obs Register.x24 (by decide) k8,
        obs_jr_other' hs.obs Register.x25 (by decide) k9,
        obs_jr_other' hs.obs Register.x26 (by decide) k10,
        obs_jr_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_jr_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_jr_other' hs.obs Register.htif_tohost (by decide) hth⟩
      mem := hs.mem.trans hc.mem
      pc := by
        rwa [show (0x8000ee58#64) + sign_extend (m := 64) (0x1fffac#21) =
          0x8000ee04#64 from by decide] at hpc
      a4 := obs_jr_other' hs.obs Register.x14 (by decide) hc.a4
      a1 := obs_jr_other' hs.obs Register.x11 (by decide) hc.a1
      ra := obs_jr_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_jr_other' hs.obs Register.x2 (by decide) hc.sp }⟩

theorem fflushEe58Arm (g : FflushG) :
    Triple (FflushAtEe58 g) (FflushAtEe04 g) := fflushEe58Arm_run g

theorem fflushAcquireReturnArm (g : FflushG) :
    Triple (FflushAtAcquire g) (FflushAtEe04 g) :=
  Triple.seq (fflushAcquireArm_ok g)
    (Triple.seq (fflushAcquireToEe50 g)
      (Triple.seq (fflushEe50Arm g)
        (Triple.seq (fflushEe54Arm g) (fflushEe58Arm g))))

def fflushEe40Lds : List (List (BitVec 8)) :=
  [flushBytes8 (0#64)]

def fflushAcquireL (g : FflushG) : GRegs :=
  [(10, 0#64), (13, 0#64), (15, 0#64),
   (14, BitVec.ofNat 64 consoleReent), (2, fflushSpE g.sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, g.ra)]

def fflushCoreKeep (g : FflushG) : GRegs :=
  [(3, wrGpVal), (8, g.s0)] ++ sKeepL g.sv

structure FflushFnPre (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = g.m0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some g.sp
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

structure FflushAtEddc (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000eddc#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

structure FflushAtEde0 (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000ede0#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  a5 : gprGet c.σ 15 = some (BitVec.ofNat 64 consoleSinit)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

structure FflushAtEde4 (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000ede4#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  a5 : gprGet c.σ 15 = some (BitVec.ofNat 64 consoleSinit)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

structure FflushEntryBase (g : FflushG) (c : Config) : Prop where
  ok : FflushGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = fflushM1 g
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s0
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

structure FflushAtEde8 (g : FflushG) (c : Config) : Prop where
  base : FflushEntryBase g c
  pc : c.σ.regs.get? Register.PC = some 0x8000ede8#64
  a3 : gprGet c.σ 13 = some 0x200a#64
  a5 : gprGet c.σ 15 = some (BitVec.ofNat 64 consoleSinit)

structure FflushAtEdec (g : FflushG) (c : Config) : Prop where
  base : FflushEntryBase g c
  pc : c.σ.regs.get? Register.PC = some 0x8000edec#64
  a3 : gprGet c.σ 13 = some 0x200a#64
  a5 : gprGet c.σ 15 = some 0#64

structure FflushAtEdf0 (g : FflushG) (c : Config) : Prop where
  base : FflushEntryBase g c
  pc : c.σ.regs.get? Register.PC = some 0x8000edf0#64
  a3 : gprGet c.σ 13 = some 0x200a#64
  a5 : gprGet c.σ 15 = some 0#64

structure FflushAtEdf4 (g : FflushG) (c : Config) : Prop where
  base : FflushEntryBase g c
  pc : c.σ.regs.get? Register.PC = some 0x8000edf4#64
  a3 : gprGet c.σ 13 = some 0x200a#64
  a5 : gprGet c.σ 15 = some 0#64

structure FflushAtEdf8 (g : FflushG) (c : Config) : Prop where
  base : FflushEntryBase g c
  pc : c.σ.regs.get? Register.PC = some 0x8000edf8#64
  a3 : gprGet c.σ 13 = some 0x200a#64
  a5 : gprGet c.σ 15 = some 0#64

structure FflushAtEdfc (g : FflushG) (c : Config) : Prop where
  base : FflushEntryBase g c
  pc : c.σ.regs.get? Register.PC = some 0x8000edfc#64
  a3 : gprGet c.σ 13 = some 0x200a#64
  a5 : gprGet c.σ 15 = some 0#64

structure FflushAtEe00 (g : FflushG) (c : Config) : Prop where
  base : FflushEntryBase g c
  pc : c.σ.regs.get? Register.PC = some 0x8000ee00#64
  a3 : gprGet c.σ 13 = some 0#64
  a5 : gprGet c.σ 15 = some 0#64

structure FflushAtEe40 (g : FflushG) (c : Config) : Prop where
  base : FflushEntryBase g c
  pc : c.σ.regs.get? Register.PC = some 0x8000ee40#64
  a3 : gprGet c.σ 13 = some 0#64
  a5 : gprGet c.σ 15 = some 0#64

def fflushM2 (g : FflushG) : Mem :=
  writeMap8 (fflushM1 g)
    (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
    (sdData_val (BitVec.ofNat 64 consoleReent))

structure FflushAtEe44 (g : FflushG) (c : Config) extends FflushPersist g c where
  mem : c.σ.mem = fflushM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee44#64
  a0 : gprGet c.σ 10 = some 0#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a3 : gprGet c.σ 13 = some 0#64
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  a5 : gprGet c.σ 15 = some 0#64
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

structure FflushAtEe48 (g : FflushG) (c : Config) extends FflushPersist g c where
  mem : c.σ.mem = fflushM2 g
  pc : c.σ.regs.get? Register.PC = some 0x8000ee48#64
  a0 : gprGet c.σ 10 = some 0#64
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a3 : gprGet c.σ 13 = some 0#64
  a4 : gprGet c.σ 14 = some (BitVec.ofNat 64 consoleReent)
  a5 : gprGet c.σ 15 = some 0#64
  ra : gprGet c.σ 1 = some g.ra
  sp : gprGet c.σ 2 = some (fflushSpE g.sp)

theorem FflushEntryBase.toPersist {g : FflushG} {c : Config}
    (h : FflushEntryBase g c) : FflushPersist g c :=
  { ok := h.ok, good := h.good, tick := h.tick, minstret := h.minstret,
    gp := h.gp, s0 := h.s0, sregs := h.sregs, out := h.out,
    pw := h.pw, th := h.th }

theorem FflushAtEde4.toEntryBase {g : FflushG} {c : Config}
    (h : FflushAtEde4 g c) : FflushEntryBase g c :=
  { ok := h.ok, good := h.good, tick := h.tick, mem := h.mem,
    minstret := h.minstret, a0 := h.a0, a1 := h.a1, a4 := h.a4,
    ra := h.ra, sp := h.sp, gp := h.gp, s0 := h.s0, sregs := h.sregs,
    out := h.out, pw := h.pw, th := h.th }

theorem fflushEntryBase_alu13 (g : FflushG) (c c' : Config)
    {pc vm v : BitVec 64} (hp : FflushEntryBase g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2) (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ
      (sigmaPost_alu c.σ pc vm Register.x13 v)) : FflushEntryBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok, good := hG, tick := hi, mem := hmem.trans hp.mem
      minstret := obs_alu_minstret hobs
      a0 := obs_alu_other' hobs Register.x10 (by decide) hp.a0
      a1 := obs_alu_other' hobs Register.x11 (by decide) hp.a1
      a4 := obs_alu_other' hobs Register.x14 (by decide) hp.a4
      ra := obs_alu_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_alu_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_alu_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_alu_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨obs_alu_other' hobs Register.x9 (by decide) k1,
        obs_alu_other' hobs Register.x18 (by decide) k2,
        obs_alu_other' hobs Register.x19 (by decide) k3,
        obs_alu_other' hobs Register.x20 (by decide) k4,
        obs_alu_other' hobs Register.x21 (by decide) k5,
        obs_alu_other' hobs Register.x22 (by decide) k6,
        obs_alu_other' hobs Register.x23 (by decide) k7,
        obs_alu_other' hobs Register.x24 (by decide) k8,
        obs_alu_other' hobs Register.x25 (by decide) k9,
        obs_alu_other' hobs Register.x26 (by decide) k10,
        obs_alu_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_alu_other' hobs Register.htif_payload_writes (by decide) hp.pw
      th := ⟨thv, obs_alu_other' hobs Register.htif_tohost (by decide) hth⟩ }

theorem fflushEntryBase_alu15 (g : FflushG) (c c' : Config)
    {pc vm v : BitVec 64} (hp : FflushEntryBase g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2) (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ
      (sigmaPost_alu c.σ pc vm Register.x15 v)) : FflushEntryBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok, good := hG, tick := hi, mem := hmem.trans hp.mem
      minstret := obs_alu_minstret hobs
      a0 := obs_alu_other' hobs Register.x10 (by decide) hp.a0
      a1 := obs_alu_other' hobs Register.x11 (by decide) hp.a1
      a4 := obs_alu_other' hobs Register.x14 (by decide) hp.a4
      ra := obs_alu_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_alu_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_alu_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_alu_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨obs_alu_other' hobs Register.x9 (by decide) k1,
        obs_alu_other' hobs Register.x18 (by decide) k2,
        obs_alu_other' hobs Register.x19 (by decide) k3,
        obs_alu_other' hobs Register.x20 (by decide) k4,
        obs_alu_other' hobs Register.x21 (by decide) k5,
        obs_alu_other' hobs Register.x22 (by decide) k6,
        obs_alu_other' hobs Register.x23 (by decide) k7,
        obs_alu_other' hobs Register.x24 (by decide) k8,
        obs_alu_other' hobs Register.x25 (by decide) k9,
        obs_alu_other' hobs Register.x26 (by decide) k10,
        obs_alu_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_alu_other' hobs Register.htif_payload_writes (by decide) hp.pw
      th := ⟨thv, obs_alu_other' hobs Register.htif_tohost (by decide) hth⟩ }

theorem fflushEntryBase_branch_nt (g : FflushG) (c c' : Config)
    {pc vm : BitVec 64} (hp : FflushEntryBase g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2) (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ (sigmaPost_branch_nottaken c.σ pc vm)) :
    FflushEntryBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok, good := hG, tick := hi, mem := hmem.trans hp.mem
      minstret := obs_branch_nottaken_minstret hobs
      a0 := obs_branch_nottaken_other' hobs Register.x10 (by decide) hp.a0
      a1 := obs_branch_nottaken_other' hobs Register.x11 (by decide) hp.a1
      a4 := obs_branch_nottaken_other' hobs Register.x14 (by decide) hp.a4
      ra := obs_branch_nottaken_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_branch_nottaken_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_branch_nottaken_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_branch_nottaken_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨obs_branch_nottaken_other' hobs Register.x9 (by decide) k1,
        obs_branch_nottaken_other' hobs Register.x18 (by decide) k2,
        obs_branch_nottaken_other' hobs Register.x19 (by decide) k3,
        obs_branch_nottaken_other' hobs Register.x20 (by decide) k4,
        obs_branch_nottaken_other' hobs Register.x21 (by decide) k5,
        obs_branch_nottaken_other' hobs Register.x22 (by decide) k6,
        obs_branch_nottaken_other' hobs Register.x23 (by decide) k7,
        obs_branch_nottaken_other' hobs Register.x24 (by decide) k8,
        obs_branch_nottaken_other' hobs Register.x25 (by decide) k9,
        obs_branch_nottaken_other' hobs Register.x26 (by decide) k10,
        obs_branch_nottaken_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_branch_nottaken_other' hobs Register.htif_payload_writes
        (by decide) hp.pw
      th := ⟨thv, obs_branch_nottaken_other' hobs Register.htif_tohost
        (by decide) hth⟩ }

theorem fflushEntryBase_branch_t (g : FflushG) (c c' : Config)
    {pc vm : BitVec 64} {imm : BitVec 13} (hp : FflushEntryBase g c)
    (hG : GoodState c'.σ) (hi : c'.tick < 2) (hmem : c'.σ.mem = c.σ.mem)
    (hobs : ReadsLikePost c'.σ (sigmaPost_branch_taken c.σ pc vm imm)) :
    FflushEntryBase g c' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
  obtain ⟨thv, hth⟩ := hp.th
  exact
    { ok := hp.ok, good := hG, tick := hi, mem := hmem.trans hp.mem
      minstret := obs_branch_taken_minstret hobs
      a0 := obs_branch_taken_other' hobs Register.x10 (by decide) hp.a0
      a1 := obs_branch_taken_other' hobs Register.x11 (by decide) hp.a1
      a4 := obs_branch_taken_other' hobs Register.x14 (by decide) hp.a4
      ra := obs_branch_taken_other' hobs Register.x1 (by decide) hp.ra
      sp := obs_branch_taken_other' hobs Register.x2 (by decide) hp.sp
      gp := obs_branch_taken_other' hobs Register.x3 (by decide) hp.gp
      s0 := obs_branch_taken_other' hobs Register.x8 (by decide) hp.s0
      sregs := ⟨obs_branch_taken_other' hobs Register.x9 (by decide) k1,
        obs_branch_taken_other' hobs Register.x18 (by decide) k2,
        obs_branch_taken_other' hobs Register.x19 (by decide) k3,
        obs_branch_taken_other' hobs Register.x20 (by decide) k4,
        obs_branch_taken_other' hobs Register.x21 (by decide) k5,
        obs_branch_taken_other' hobs Register.x22 (by decide) k6,
        obs_branch_taken_other' hobs Register.x23 (by decide) k7,
        obs_branch_taken_other' hobs Register.x24 (by decide) k8,
        obs_branch_taken_other' hobs Register.x25 (by decide) k9,
        obs_branch_taken_other' hobs Register.x26 (by decide) k10,
        obs_branch_taken_other' hobs Register.x27 (by decide) k11, trivial⟩
      out := hobs.2.trans hp.out
      pw := obs_branch_taken_other' hobs Register.htif_payload_writes
        (by decide) hp.pw
      th := ⟨thv, obs_branch_taken_other' hobs Register.htif_tohost
        (by decide) hth⟩ }

theorem fflushEdccArm (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEddc g) := by
  have T := segRowFramed fflush_rXedccFSeg (fflushPrefixL g) fflushPrefixLds
    0x8000edcc#64 g.m0 (fflushCoreKeep g) g.out0 (0#4)
    (by
      show ChainOK 0x8000edcc#64 [11, 2, 1, 10] fflush_rXedccFSeg
      decide)
    (by
      show FrameOK [3, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
        fflush_rXedccFSeg
      decide)
  intro c hc
  obtain ⟨hpc, hp⟩ := hc
  have hkeys : KeysOK (keysG (fflushPrefixL g)) := by
    change KeysOK [11, 2, 1, 10]
    decide
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (fflushPrefixL g) fflushPrefixLds fflush_rXedccFSeg := by
    rw [hp.mem]
    exact fflushEdcc_facts g hp.ok
  obtain ⟨c1, hs, h1⟩ := T c
    { seg := ⟨hp.good, hp.mem, hpc, hp.minstret,
          ⟨hp.a1, hp.sp, hp.ra, hp.a0, trivial⟩,
          hkeys, hfacts, hp.tick⟩
      keep := ⟨hp.gp, hp.s0, hp.sregs⟩
      out := hp.out
      pw := hp.pw
      th := hp.th }
  have hregs : GHolds c1.σ (fflushL1 g) := by
    have hr := h1.regs
    rw [evalBlocks_regs] at hr
    change GHolds c1.σ
      (runChain fflush_rXedccFSeg (fflushPrefixL g) fflushPrefixLds) at hr
    have he : runChain fflush_rXedccFSeg (fflushPrefixL g) fflushPrefixLds =
        fflushL1 g := by rfl
    rwa [he] at hr
  obtain ⟨kgp, ks0, ksregs⟩ := h1.keep
  exact ⟨c1, hs,
    { ok := hp.ok
      good := h1.good
      tick := h1.tick
      mem := by simpa [fflushM1] using h1.mem
      pc := by simpa using h1.pc
      minstret := h1.minstret
      a0 := gholds_lookup (v := BitVec.ofNat 64 consoleReent) _ hregs (by rfl)
      a1 := gholds_lookup (v := BitVec.ofNat 64 consoleStdout) _ hregs (by rfl)
      a4 := gholds_lookup (v := BitVec.ofNat 64 consoleReent) _ hregs (by rfl)
      ra := gholds_lookup (v := g.ra) _ hregs (by rfl)
      sp := gholds_lookup (v := fflushSpE g.sp) _ hregs (by rfl)
      gp := kgp
      s0 := ks0
      sregs := ksregs
      out := h1.out
      pw := h1.pw
      th := h1.th }⟩

theorem fflushM1_at_eddc (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000eddc]? = some 0x83#8 ∧
    (fflushM1 g)[0x8000eddd]? = some 0x37#8 ∧
    (fflushM1 g)[0x8000edde]? = some 0x85#8 ∧
    (fflushM1 g)[0x8000eddf]? = some 0x04#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000eddc hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000eddf + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hb0,
    by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hb1,
    by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hb2,
    by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hb3⟩

theorem fflushEddc_ld_site (σ : MState) (i u : Nat) (vminstret v10 : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000eddc#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hb0 : σ.mem[0x8000eddc]? = some 0x83#8)
    (hb1 : σ.mem[0x8000eddd]? = some 0x37#8)
    (hb2 : σ.mem[0x8000edde]? = some 0x85#8)
    (hb3 : σ.mem[0x8000eddf]? = some 0x04#8)
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x048#12)).toNat)
    (hhi : (v10 + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤
      0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤
      tohostAddr ∨ tohostAddr + 8 ≤
        (v10 + sign_extend (m := 64) (0x048#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x048#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ (0x8000eddc#64) vminstret Register.x15
          (sign_extend (m := 64)
            (bytesT8 σ.mem
              (v10 + sign_extend (m := 64) (0x048#12)).toNat : BitVec (8 * 8)))) := by
  exact stepObs_alu σ i u (0x8000eddc#64) vminstret (0x04853783#32)
    (instruction.LOAD (0x048#12, regidx.Regidx 0x0a#5,
      regidx.Regidx 0x0f#5, false, 8)) Register.x15
    (sign_extend (m := 64)
      (bytesT8 σ.mem
        (v10 + sign_extend (m := 64) (0x048#12)).toNat : BitVec (8 * 8)))
    (0x83#8) (0x37#8) (0x85#8) (0x04#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_04853783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_tot σ (0x8000eddc#64) (0x048#12)
      (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x8000eddc#64) Register.x15
        (sign_extend (m := 64)
          (bytesT8 σ.mem
            (v10 + sign_extend (m := 64) (0x048#12)).toNat : BitVec (8 * 8))))
      v10 hG
      (rX_bits_x10 _ v10 (by
        rw [get?_afterNextPC σ (0x8000eddc#64) _ (by decide) (by decide)]
        exact hx10))
      (wX_bits_x15 _
        (sign_extend (m := 64)
          (bytesT8 σ.mem
            (v10 + sign_extend (m := 64) (0x048#12)).toNat : BitVec (8 * 8))))
      hlo hhi hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEddcStep (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = BitVec.ofNat 64 consoleSinit
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000eddc#64) vm Register.x15 loaded)

theorem fflushEddcStep_run (g : FflushG) (c : Config)
    (hc : FflushAtEddc g c) : ∃ vm loaded c1, FflushEddcStep g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_eddc g hc.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEddc_ld_site c.σ c.tick c.steps vm
      (BitVec.ofNat 64 consoleReent) hc.good hc.pc hmi hc.a0
      (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem])
      (by decide) (by decide) (by right; decide) (by decide) hc.tick
  let loaded := sign_extend (m := 64)
    (bytesT8 c.σ.mem
      (BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x048#12)).toNat :
        BitVec (8 * 8))
  have heq : loaded = BitVec.ofNat 64 consoleSinit := by
    unfold loaded
    have haddr :
        (BitVec.ofNat 64 consoleReent + sign_extend (m := 64) (0x048#12)).toNat =
          consoleReent + 72 := by decide
    rw [haddr]
    have hp : LPins8 c.σ.mem (consoleReent + 72)
        (flushBytes8 (BitVec.ofNat 64 consoleSinit)) := by
      rw [hc.mem, fflushM1_eq]
      refine lpins8_writeMap8_disjoint _ _ ?_ ?_
      · left
        rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
          fflush_slot_toNat g.sp hc.ok.stack 24 (by decide)]
        have hn := hc.ok.stack.nested.console
        rw [fflush_spE_toNat g.sp hc.ok.stack] at hn
        dsimp [consoleReent, consoleStdout] at *
        omega
      · apply fflush_lpins8_of_read64 _ _ _ _ _ _ _ _ hc.ok.console.sinit
        decide
    rw [bytesT8_of_lpins8 hp]
    decide
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEddcArm_run (g : FflushG) (c : Config)
    (hc : FflushAtEddc g c) : ∃ c', Steps c c' ∧ FflushAtEde0 g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEddcStep_run g c hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  have hpc := obs_alu_pc hs.obs
  have ha5 := obs_gpr_rd 15 (by decide) (by decide) loaded hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      mem := hs.mem.trans hc.mem
      pc := by
        rwa [show BitVec.addInt (0x8000eddc#64) 4 = 0x8000ede0#64 from by decide]
          at hpc
      minstret := obs_alu_minstret hs.obs
      a0 := obs_alu_other' hs.obs Register.x10 (by decide) hc.a0
      a1 := obs_alu_other' hs.obs Register.x11 (by decide) hc.a1
      a4 := obs_alu_other' hs.obs Register.x14 (by decide) hc.a4
      a5 := by rwa [hs.loaded_eq] at ha5
      ra := obs_alu_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_alu_other' hs.obs Register.x2 (by decide) hc.sp
      gp := obs_alu_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_alu_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_alu_other' hs.obs Register.x9 (by decide) k1,
        obs_alu_other' hs.obs Register.x18 (by decide) k2,
        obs_alu_other' hs.obs Register.x19 (by decide) k3,
        obs_alu_other' hs.obs Register.x20 (by decide) k4,
        obs_alu_other' hs.obs Register.x21 (by decide) k5,
        obs_alu_other' hs.obs Register.x22 (by decide) k6,
        obs_alu_other' hs.obs Register.x23 (by decide) k7,
        obs_alu_other' hs.obs Register.x24 (by decide) k8,
        obs_alu_other' hs.obs Register.x25 (by decide) k9,
        obs_alu_other' hs.obs Register.x26 (by decide) k10,
        obs_alu_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_alu_other' hs.obs Register.htif_payload_writes (by decide) hc.pw
      th := ⟨thv, obs_alu_other' hs.obs Register.htif_tohost (by decide) hth⟩ }⟩

theorem fflushEddcArm (g : FflushG) :
    Triple (FflushAtEddc g) (FflushAtEde0 g) := fflushEddcArm_run g

theorem fflushM1_at_ede0 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000ede0]? = some 0x63#8 ∧
    (fflushM1 g)[0x8000ede1]? = some 0x8e#8 ∧
    (fflushM1 g)[0x8000ede2]? = some 0x07#8 ∧
    (fflushM1 g)[0x8000ede3]? = some 0x08#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ede0 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000ede3 + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hb0,
    by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hb1,
    by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hb2,
    by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hb3⟩

theorem fflushEde0_branch_site (σ : MState) (i u : Nat) (vminstret v15 : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000ede0#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hb0 : σ.mem[0x8000ede0]? = some 0x63#8)
    (hb1 : σ.mem[0x8000ede1]? = some 0x8e#8)
    (hb2 : σ.mem[0x8000ede2]? = some 0x07#8)
    (hb3 : σ.mem[0x8000ede3]? = some 0x08#8)
    (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_branch_nottaken σ (0x8000ede0#64) vminstret) := by
  exact stepObs_branch_nottaken σ i u (0x8000ede0#64) vminstret (0x009c#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x08078e63#32)
    (0x63#8) (0x8e#8) (0x07#8) (0x08#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_08078e63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x009c#13) (regidx.Regidx 0x0f#5)
      (regidx.Regidx 0x00#5) v15 (0#64)
      (afterNextPC (afterPrelude σ) (0x8000ede0#64))
      (rX_bits_x15 _ v15 (by
        rw [get?_afterNextPC σ (0x8000ede0#64) _ (by decide) (by decide)]
        exact hx15))
      (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEde0Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_branch_nottaken c.σ (0x8000ede0#64) vm)

theorem fflushEde0Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEde0 g c) : ∃ vm c1, FflushEde0Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_ede0 g hc.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEde0_branch_site c.σ c.tick c.steps vm
      (BitVec.ofNat 64 consoleSinit) hc.good hc.pc hmi hc.a5
      (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem])
      (by decide) hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEde0Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEde0 g c) : ∃ c', Steps c c' ∧ FflushAtEde4 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEde0Step_run g c hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hc.sregs
  obtain ⟨thv, hth⟩ := hc.th
  have hpc := obs_branch_nottaken_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { ok := hc.ok
      good := hs.good
      tick := hs.tick
      mem := hs.mem.trans hc.mem
      pc := by
        rwa [show BitVec.addInt (0x8000ede0#64) 4 = 0x8000ede4#64 from by decide]
          at hpc
      minstret := obs_branch_nottaken_minstret hs.obs
      a0 := obs_branch_nottaken_other' hs.obs Register.x10 (by decide) hc.a0
      a1 := obs_branch_nottaken_other' hs.obs Register.x11 (by decide) hc.a1
      a4 := obs_branch_nottaken_other' hs.obs Register.x14 (by decide) hc.a4
      a5 := obs_branch_nottaken_other' hs.obs Register.x15 (by decide) hc.a5
      ra := obs_branch_nottaken_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_branch_nottaken_other' hs.obs Register.x2 (by decide) hc.sp
      gp := obs_branch_nottaken_other' hs.obs Register.x3 (by decide) hc.gp
      s0 := obs_branch_nottaken_other' hs.obs Register.x8 (by decide) hc.s0
      sregs := ⟨
        obs_branch_nottaken_other' hs.obs Register.x9 (by decide) k1,
        obs_branch_nottaken_other' hs.obs Register.x18 (by decide) k2,
        obs_branch_nottaken_other' hs.obs Register.x19 (by decide) k3,
        obs_branch_nottaken_other' hs.obs Register.x20 (by decide) k4,
        obs_branch_nottaken_other' hs.obs Register.x21 (by decide) k5,
        obs_branch_nottaken_other' hs.obs Register.x22 (by decide) k6,
        obs_branch_nottaken_other' hs.obs Register.x23 (by decide) k7,
        obs_branch_nottaken_other' hs.obs Register.x24 (by decide) k8,
        obs_branch_nottaken_other' hs.obs Register.x25 (by decide) k9,
        obs_branch_nottaken_other' hs.obs Register.x26 (by decide) k10,
        obs_branch_nottaken_other' hs.obs Register.x27 (by decide) k11, trivial⟩
      out := hs.obs.2.trans hc.out
      pw := obs_branch_nottaken_other' hs.obs Register.htif_payload_writes
        (by decide) hc.pw
      th := ⟨thv, obs_branch_nottaken_other' hs.obs Register.htif_tohost
        (by decide) hth⟩ }⟩

theorem fflushEde0Arm (g : FflushG) :
    Triple (FflushAtEde0 g) (FflushAtEde4 g) := fflushEde0Arm_run g

theorem fflushM1_at_ede4 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000ede4]? = some 0x83#8 ∧
    (fflushM1 g)[0x8000ede5]? = some 0x96#8 ∧
    (fflushM1 g)[0x8000ede6]? = some 0x05#8 ∧
    (fflushM1 g)[0x8000ede7]? = some 0x01#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ede4 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000ede7 + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushM1_flag_bytes (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[consoleStdout + 16]? = some 0x0a#8 ∧
    (fflushM1 g)[consoleStdout + 17]? = some 0x20#8 := by
  rw [fflushM1_eq]
  have hdis : consoleStdout + 18 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.console
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    dsimp [consoleStdout] at *
    omega
  exact ⟨by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hg.console.flag0,
    by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]
      exact hg.console.flag1⟩

theorem fflushEde4_lh_site (σ : MState) (i u : Nat) (vminstret v11 : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000ede4#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hb0 : σ.mem[0x8000ede4]? = some 0x83#8)
    (hb1 : σ.mem[0x8000ede5]? = some 0x96#8)
    (hb2 : σ.mem[0x8000ede6]? = some 0x05#8)
    (hb3 : σ.mem[0x8000ede7]? = some 0x01#8)
    (hv : sign_extend (m := 64)
      (bytesT2 σ.mem
        (v11 + sign_extend (m := 64) (0x010#12)).toNat : BitVec (8 * 2)) =
        0x200a#64)
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhi : (v11 + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤
      0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤
        tohostAddr ∨ tohostAddr + 8 ≤
          (v11 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x010#12)).toNat % 2 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ (0x8000ede4#64) vminstret Register.x13 0x200a#64) := by
  exact stepObs_alu σ i u (0x8000ede4#64) vminstret (0x01059683#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0b#5,
      regidx.Regidx 0x0d#5, false, 2)) Register.x13 0x200a#64
    (0x83#8) (0x96#8) (0x05#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01059683 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lh_totv σ (0x8000ede4#64) (0x010#12)
      (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0d#5)
      (sigma3_alu σ (0x8000ede4#64) Register.x13 0x200a#64)
      v11 0x200a#64 hG
      (rX_bits_x11 _ v11 (by
        rw [get?_afterNextPC σ (0x8000ede4#64) _ (by decide) (by decide)]
        exact hx11))
      hv (wX_bits_x13 _ 0x200a#64)
      hlo hhi hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEde4Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ede4#64) vm Register.x13 0x200a#64)

theorem fflushEde4Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEde4 g c) : ∃ vm c1, FflushEde4Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_ede4 g hc.ok
  obtain ⟨hd0, hd1⟩ := fflushM1_flag_bytes g hc.ok
  have hv : sign_extend (m := 64)
      (bytesT2 c.σ.mem
        (BitVec.ofNat 64 consoleStdout + sign_extend (m := 64) (0x010#12)).toNat :
          BitVec (8 * 2)) = 0x200a#64 := by
    have ha : (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x010#12)).toNat = consoleStdout + 16 := by decide
    have hp0 : ((c.σ.mem[consoleStdout + 16]?).getD 0) = 0x0a#8 := by
      rw [hc.mem]
      exact lpin_of_present hd0
    have hp1 : ((c.σ.mem[consoleStdout + 17]?).getD 0) = 0x20#8 := by
      rw [hc.mem]
      exact lpin_of_present hd1
    rw [ha, bytesT2_of_pins hp0 hp1]
    decide
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEde4_lh_site c.σ c.tick c.steps vm
      (BitVec.ofNat 64 consoleStdout) hc.good hc.pc hmi hc.a1
      (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem])
      hv (by decide) (by decide) (by right; decide) (by decide) hc.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEde4Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEde4 g c) : ∃ c', Steps c c' ∧ FflushAtEde8 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEde4Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { base := fflushEntryBase_alu13 g c c1 hc.toEntryBase
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000ede4#64) 4 = 0x8000ede8#64 from by decide]
          at hpc
      a3 := obs_gpr_rd 13 (by decide) (by decide) 0x200a#64 hs.obs
      a5 := obs_alu_other' hs.obs Register.x15 (by decide) hc.a5 }⟩

theorem fflushEde4Arm (g : FflushG) :
    Triple (FflushAtEde4 g) (FflushAtEde8 g) := fflushEde4Arm_run g

theorem fflushM1_at_ede8 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000ede8]? = some 0x93#8 ∧
    (fflushM1 g)[0x8000ede9]? = some 0x07#8 ∧
    (fflushM1 g)[0x8000edea]? = some 0x00#8 ∧
    (fflushM1 g)[0x8000edeb]? = some 0x00#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ede8 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000edeb + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEde8_li_site (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000ede8#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[0x8000ede8]? = some 0x93#8)
    (hb1 : σ.mem[0x8000ede9]? = some 0x07#8)
    (hb2 : σ.mem[0x8000edea]? = some 0x00#8)
    (hb3 : σ.mem[0x8000edeb]? = some 0x00#8)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ (0x8000ede8#64) vminstret Register.x15 0#64) := by
  exact stepObs_alu σ i u (0x8000ede8#64) vminstret (0x00000793#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5,
      regidx.Regidx 0x0f#5, iop.ADDI)) Register.x15 0#64
    (0x93#8) (0x07#8) (0x00#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00000793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5)
      (regidx.Regidx 0x0f#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x8000ede8#64))
      (sigma3_alu σ (0x8000ede8#64) Register.x15 0#64)
      (rX_bits_zero _) (wX_bits_x15 _ 0#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEde8Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ede8#64) vm Register.x15 0#64)

theorem fflushEde8Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEde8 g c) : ∃ vm c1, FflushEde8Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.base.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_ede8 g hc.base.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEde8_li_site c.σ c.tick c.steps vm hc.base.good hc.pc hmi
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem]) hc.base.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEde8Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEde8 g c) : ∃ c', Steps c c' ∧ FflushAtEdec g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEde8Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { base := fflushEntryBase_alu15 g c c1 hc.base
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000ede8#64) 4 = 0x8000edec#64 from by decide]
          at hpc
      a3 := obs_alu_other' hs.obs Register.x13 (by decide) hc.a3
      a5 := obs_gpr_rd 15 (by decide) (by decide) 0#64 hs.obs }⟩

theorem fflushEde8Arm (g : FflushG) :
    Triple (FflushAtEde8 g) (FflushAtEdec g) := fflushEde8Arm_run g

theorem fflushM1_at_edec (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000edec]? = some 0x63#8 ∧
    (fflushM1 g)[0x8000eded]? = some 0x82#8 ∧
    (fflushM1 g)[0x8000edee]? = some 0x06#8 ∧
    (fflushM1 g)[0x8000edef]? = some 0x04#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000edec hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000edef + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEdec_branch_site (σ : MState) (i u : Nat) (vminstret v13 : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000edec#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hb0 : σ.mem[0x8000edec]? = some 0x63#8)
    (hb1 : σ.mem[0x8000eded]? = some 0x82#8)
    (hb2 : σ.mem[0x8000edee]? = some 0x06#8)
    (hb3 : σ.mem[0x8000edef]? = some 0x04#8)
    (hv : (v13 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_branch_nottaken σ (0x8000edec#64) vminstret) := by
  exact stepObs_branch_nottaken σ i u (0x8000edec#64) vminstret (0x0044#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BEQ (0x04068263#32)
    (0x63#8) (0x82#8) (0x06#8) (0x04#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_04068263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x0044#13) (regidx.Regidx 0x0d#5)
      (regidx.Regidx 0x00#5) v13 (0#64)
      (afterNextPC (afterPrelude σ) (0x8000edec#64))
      (rX_bits_x13 _ v13 (by
        rw [get?_afterNextPC σ (0x8000edec#64) _ (by decide) (by decide)]
        exact hx13))
      (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEdecStep (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_branch_nottaken c.σ (0x8000edec#64) vm)

theorem fflushEdecStep_run (g : FflushG) (c : Config)
    (hc : FflushAtEdec g c) : ∃ vm c1, FflushEdecStep g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.base.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_edec g hc.base.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEdec_branch_site c.σ c.tick c.steps vm 0x200a#64
      hc.base.good hc.pc hmi hc.a3
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem]) (by decide) hc.base.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEdecArm_run (g : FflushG) (c : Config)
    (hc : FflushAtEdec g c) : ∃ c', Steps c c' ∧ FflushAtEdf0 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEdecStep_run g c hc
  have hpc := obs_branch_nottaken_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { base := fflushEntryBase_branch_nt g c c1 hc.base
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000edec#64) 4 = 0x8000edf0#64 from by decide]
          at hpc
      a3 := obs_branch_nottaken_other' hs.obs Register.x13 (by decide) hc.a3
      a5 := obs_branch_nottaken_other' hs.obs Register.x15 (by decide) hc.a5 }⟩

theorem fflushEdecArm (g : FflushG) :
    Triple (FflushAtEdec g) (FflushAtEdf0 g) := fflushEdecArm_run g

theorem fflushM1_at_edf0 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000edf0]? = some 0x83#8 ∧
    (fflushM1 g)[0x8000edf1]? = some 0xa7#8 ∧
    (fflushM1 g)[0x8000edf2]? = some 0x05#8 ∧
    (fflushM1 g)[0x8000edf3]? = some 0x0b#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000edf0 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000edf3 + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEdf0_lw_site (σ : MState) (i u : Nat) (vminstret v11 : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000edf0#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hb0 : σ.mem[0x8000edf0]? = some 0x83#8)
    (hb1 : σ.mem[0x8000edf1]? = some 0xa7#8)
    (hb2 : σ.mem[0x8000edf2]? = some 0x05#8)
    (hb3 : σ.mem[0x8000edf3]? = some 0x0b#8)
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x0b0#12)).toNat)
    (hhi : (v11 + sign_extend (m := 64) (0x0b0#12)).toNat + 4 ≤
      0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x0b0#12)).toNat + 4 ≤
        tohostAddr ∨ tohostAddr + 8 ≤
          (v11 + sign_extend (m := 64) (0x0b0#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x0b0#12)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ (0x8000edf0#64) vminstret Register.x15
          (sign_extend (m := 64)
            (bytesT4 σ.mem
              (v11 + sign_extend (m := 64) (0x0b0#12)).toNat : BitVec (8 * 4)))) := by
  exact stepObs_alu σ i u (0x8000edf0#64) vminstret (0x0b05a783#32)
    (instruction.LOAD (0x0b0#12, regidx.Regidx 0x0b#5,
      regidx.Regidx 0x0f#5, false, 4)) Register.x15
    (sign_extend (m := 64)
      (bytesT4 σ.mem
        (v11 + sign_extend (m := 64) (0x0b0#12)).toNat : BitVec (8 * 4)))
    (0x83#8) (0xa7#8) (0x05#8) (0x0b#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0b05a783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw_tot σ (0x8000edf0#64) (0x0b0#12)
      (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x8000edf0#64) Register.x15
        (sign_extend (m := 64)
          (bytesT4 σ.mem
            (v11 + sign_extend (m := 64) (0x0b0#12)).toNat : BitVec (8 * 4))))
      v11 hG
      (rX_bits_x11 _ v11 (by
        rw [get?_afterNextPC σ (0x8000edf0#64) _ (by decide) (by decide)]
        exact hx11))
      (wX_bits_x15 _
        (sign_extend (m := 64)
          (bytesT4 σ.mem
            (v11 + sign_extend (m := 64) (0x0b0#12)).toNat : BitVec (8 * 4))))
      hlo hhi hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEdf0Step (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = 0#64
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000edf0#64) vm Register.x15 loaded)

theorem fflushEdf0Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEdf0 g c) : ∃ vm loaded c1, FflushEdf0Step g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.base.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_edf0 g hc.base.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEdf0_lw_site c.σ c.tick c.steps vm
      (BitVec.ofNat 64 consoleStdout) hc.base.good hc.pc hmi hc.base.a1
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by decide) (by decide) (by right; decide) (by decide) hc.base.tick
  let loaded := sign_extend (m := 64)
    (bytesT4 c.σ.mem
      (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x0b0#12)).toNat : BitVec (8 * 4))
  have heq : loaded = 0#64 := by
    unfold loaded
    have hp : LPins4 c.σ.mem (consoleStdout + 176)
        [0#8, 0#8, 0#8, 0#8] := by
      rw [hc.base.mem, fflushM1_eq]
      refine fflush_lpins4_write8 _ ?_ (fflush_lpins4_zero hc.base.ok.console.lockMode)
      left
      rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
        fflush_slot_toNat g.sp hc.base.ok.stack 24 (by decide)]
      have hn := hc.base.ok.stack.nested.console
      rw [fflush_spE_toNat g.sp hc.base.ok.stack] at hn
      dsimp [consoleStdout] at *
      omega
    have haddr : (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x0b0#12)).toNat = consoleStdout + 176 := by decide
    rw [haddr, bytesT4_of_lpins4 hp]
    decide
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEdf0Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEdf0 g c) : ∃ c', Steps c c' ∧ FflushAtEdf4 g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEdf0Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have ha5 := obs_gpr_rd 15 (by decide) (by decide) loaded hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { base := fflushEntryBase_alu15 g c c1 hc.base
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000edf0#64) 4 = 0x8000edf4#64 from by decide]
          at hpc
      a3 := obs_alu_other' hs.obs Register.x13 (by decide) hc.a3
      a5 := by rwa [hs.loaded_eq] at ha5 }⟩

theorem fflushEdf0Arm (g : FflushG) :
    Triple (FflushAtEdf0 g) (FflushAtEdf4 g) := fflushEdf0Arm_run g

theorem fflushM1_at_edf4 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000edf4]? = some 0x93#8 ∧
    (fflushM1 g)[0x8000edf5]? = some 0xf7#8 ∧
    (fflushM1 g)[0x8000edf6]? = some 0x17#8 ∧
    (fflushM1 g)[0x8000edf7]? = some 0x00#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000edf4 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000edf7 + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEdf4_andi_site (σ : MState) (i u : Nat)
    (vminstret v15 : BitVec 64) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000edf4#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hb0 : σ.mem[0x8000edf4]? = some 0x93#8)
    (hb1 : σ.mem[0x8000edf5]? = some 0xf7#8)
    (hb2 : σ.mem[0x8000edf6]? = some 0x17#8)
    (hb3 : σ.mem[0x8000edf7]? = some 0x00#8)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ (0x8000edf4#64) vminstret Register.x15
          (v15 &&& sign_extend (m := 64) (0x001#12))) := by
  exact stepObs_alu σ i u (0x8000edf4#64) vminstret (0x0017f793#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0f#5,
      regidx.Regidx 0x0f#5, iop.ANDI)) Register.x15
    (v15 &&& sign_extend (m := 64) (0x001#12))
    (0x93#8) (0xf7#8) (0x17#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0017f793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_andi_char (0x001#12) (regidx.Regidx 0x0f#5)
      (regidx.Regidx 0x0f#5) v15
      (afterNextPC (afterPrelude σ) (0x8000edf4#64))
      (sigma3_alu σ (0x8000edf4#64) Register.x15
        (v15 &&& sign_extend (m := 64) (0x001#12)))
      (rX_bits_x15 _ v15 (by
        rw [get?_afterNextPC σ (0x8000edf4#64) _ (by decide) (by decide)]
        exact hx15))
      (wX_bits_x15 _ (v15 &&& sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEdf4Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000edf4#64) vm Register.x15
      (0#64 &&& sign_extend (m := 64) (0x001#12)))

theorem fflushEdf4Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEdf4 g c) : ∃ vm c1, FflushEdf4Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.base.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_edf4 g hc.base.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEdf4_andi_site c.σ c.tick c.steps vm 0#64 hc.base.good hc.pc hmi hc.a5
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem]) hc.base.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEdf4Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEdf4 g c) : ∃ c', Steps c c' ∧ FflushAtEdf8 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEdf4Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { base := fflushEntryBase_alu15 g c c1 hc.base
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000edf4#64) 4 = 0x8000edf8#64 from by decide]
          at hpc
      a3 := obs_alu_other' hs.obs Register.x13 (by decide) hc.a3
      a5 := by
        have h := obs_gpr_rd 15 (by decide) (by decide)
          (0#64 &&& sign_extend (m := 64) (0x001#12)) hs.obs
        simpa using h }⟩

theorem fflushEdf4Arm (g : FflushG) :
    Triple (FflushAtEdf4 g) (FflushAtEdf8 g) := fflushEdf4Arm_run g

theorem fflushM1_at_edf8 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000edf8]? = some 0x63#8 ∧
    (fflushM1 g)[0x8000edf9]? = some 0x96#8 ∧
    (fflushM1 g)[0x8000edfa]? = some 0x07#8 ∧
    (fflushM1 g)[0x8000edfb]? = some 0x00#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000edf8 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000edfb + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEdf8_branch_site (σ : MState) (i u : Nat)
    (vminstret v15 : BitVec 64) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000edf8#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hb0 : σ.mem[0x8000edf8]? = some 0x63#8)
    (hb1 : σ.mem[0x8000edf9]? = some 0x96#8)
    (hb2 : σ.mem[0x8000edfa]? = some 0x07#8)
    (hb3 : σ.mem[0x8000edfb]? = some 0x00#8)
    (hv : (v15 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_branch_nottaken σ (0x8000edf8#64) vminstret) := by
  exact stepObs_branch_nottaken σ i u (0x8000edf8#64) vminstret (0x000c#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0x00079663#32)
    (0x63#8) (0x96#8) (0x07#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00079663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_nottaken (0x000c#13) (regidx.Regidx 0x0f#5)
      (regidx.Regidx 0x00#5) v15 (0#64)
      (afterNextPC (afterPrelude σ) (0x8000edf8#64))
      (rX_bits_x15 _ v15 (by
        rw [get?_afterNextPC σ (0x8000edf8#64) _ (by decide) (by decide)]
        exact hx15))
      (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEdf8Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_branch_nottaken c.σ (0x8000edf8#64) vm)

theorem fflushEdf8Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEdf8 g c) : ∃ vm c1, FflushEdf8Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.base.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_edf8 g hc.base.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEdf8_branch_site c.σ c.tick c.steps vm 0#64 hc.base.good hc.pc hmi hc.a5
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem]) (by decide) hc.base.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEdf8Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEdf8 g c) : ∃ c', Steps c c' ∧ FflushAtEdfc g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEdf8Step_run g c hc
  have hpc := obs_branch_nottaken_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { base := fflushEntryBase_branch_nt g c c1 hc.base
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000edf8#64) 4 = 0x8000edfc#64 from by decide]
          at hpc
      a3 := obs_branch_nottaken_other' hs.obs Register.x13 (by decide) hc.a3
      a5 := obs_branch_nottaken_other' hs.obs Register.x15 (by decide) hc.a5 }⟩

theorem fflushEdf8Arm (g : FflushG) :
    Triple (FflushAtEdf8 g) (FflushAtEdfc g) := fflushEdf8Arm_run g

theorem fflushM1_at_edfc (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000edfc]? = some 0x93#8 ∧
    (fflushM1 g)[0x8000edfd]? = some 0xf6#8 ∧
    (fflushM1 g)[0x8000edfe]? = some 0x06#8 ∧
    (fflushM1 g)[0x8000edff]? = some 0x20#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000edfc hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000edff + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEdfc_andi_site (σ : MState) (i u : Nat)
    (vminstret v13 : BitVec 64) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000edfc#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hb0 : σ.mem[0x8000edfc]? = some 0x93#8)
    (hb1 : σ.mem[0x8000edfd]? = some 0xf6#8)
    (hb2 : σ.mem[0x8000edfe]? = some 0x06#8)
    (hb3 : σ.mem[0x8000edff]? = some 0x20#8)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ (0x8000edfc#64) vminstret Register.x13
          (v13 &&& sign_extend (m := 64) (0x200#12))) := by
  exact stepObs_alu σ i u (0x8000edfc#64) vminstret (0x2006f693#32)
    (instruction.ITYPE (0x200#12, regidx.Regidx 0x0d#5,
      regidx.Regidx 0x0d#5, iop.ANDI)) Register.x13
    (v13 &&& sign_extend (m := 64) (0x200#12))
    (0x93#8) (0xf6#8) (0x06#8) (0x20#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_2006f693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_andi_char (0x200#12) (regidx.Regidx 0x0d#5)
      (regidx.Regidx 0x0d#5) v13
      (afterNextPC (afterPrelude σ) (0x8000edfc#64))
      (sigma3_alu σ (0x8000edfc#64) Register.x13
        (v13 &&& sign_extend (m := 64) (0x200#12)))
      (rX_bits_x13 _ v13 (by
        rw [get?_afterNextPC σ (0x8000edfc#64) _ (by decide) (by decide)]
        exact hx13))
      (wX_bits_x13 _ (v13 &&& sign_extend (m := 64) (0x200#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEdfcStep (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000edfc#64) vm Register.x13
      (0x200a#64 &&& sign_extend (m := 64) (0x200#12)))

theorem fflushEdfcStep_run (g : FflushG) (c : Config)
    (hc : FflushAtEdfc g c) : ∃ vm c1, FflushEdfcStep g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.base.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_edfc g hc.base.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEdfc_andi_site c.σ c.tick c.steps vm 0x200a#64
      hc.base.good hc.pc hmi hc.a3
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem]) hc.base.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEdfcArm_run (g : FflushG) (c : Config)
    (hc : FflushAtEdfc g c) : ∃ c', Steps c c' ∧ FflushAtEe00 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEdfcStep_run g c hc
  have hpc := obs_alu_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { base := fflushEntryBase_alu13 g c c1 hc.base
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show BitVec.addInt (0x8000edfc#64) 4 = 0x8000ee00#64 from by decide]
          at hpc
      a3 := by
        have h := obs_gpr_rd 13 (by decide) (by decide)
          (0x200a#64 &&& sign_extend (m := 64) (0x200#12)) hs.obs
        simpa using h
      a5 := obs_alu_other' hs.obs Register.x15 (by decide) hc.a5 }⟩

theorem fflushEdfcArm (g : FflushG) :
    Triple (FflushAtEdfc g) (FflushAtEe00 g) := fflushEdfcArm_run g

theorem fflushM1_at_ee00 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000ee00]? = some 0x63#8 ∧
    (fflushM1 g)[0x8000ee01]? = some 0x80#8 ∧
    (fflushM1 g)[0x8000ee02]? = some 0x06#8 ∧
    (fflushM1 g)[0x8000ee03]? = some 0x04#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee00 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000ee03 + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEe00_branch_site (σ : MState) (i u : Nat)
    (vminstret v13 : BitVec 64) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000ee00#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hb0 : σ.mem[0x8000ee00]? = some 0x63#8)
    (hb1 : σ.mem[0x8000ee01]? = some 0x80#8)
    (hb2 : σ.mem[0x8000ee02]? = some 0x06#8)
    (hb3 : σ.mem[0x8000ee03]? = some 0x04#8)
    (hv : (v13 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_branch_taken σ (0x8000ee00#64) vminstret (0x0040#13)) := by
  exact stepObs_branch_taken σ i u (0x8000ee00#64) vminstret (0x0040#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BEQ (0x04068063#32)
    (0x63#8) (0x80#8) (0x06#8) (0x04#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_04068063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_taken (0x0040#13) (regidx.Regidx 0x0d#5)
      (regidx.Regidx 0x00#5) v13 (0#64) (0x8000ee00#64) initMisa
      (afterNextPC (afterPrelude σ) (0x8000ee00#64))
      (rX_bits_x13 _ v13 (by
        rw [get?_afterNextPC σ (0x8000ee00#64) _ (by decide) (by decide)]
        exact hx13))
      (rX_bits_zero _)
      (by rw [get?_afterNextPC σ (0x8000ee00#64) _ (by decide) (by decide)]
          exact hpc)
      (by rw [get?_afterNextPC σ (0x8000ee00#64) _ (by decide) (by decide)]
          exact hG.misa)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe00Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  obs : ReadsLikePost c1.σ
    (sigmaPost_branch_taken c.σ (0x8000ee00#64) vm (0x0040#13))

theorem fflushEe00Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe00 g c) : ∃ vm c1, FflushEe00Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.base.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_ee00 g hc.base.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe00_branch_site c.σ c.tick c.steps vm 0#64 hc.base.good hc.pc hmi hc.a3
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem]) (by decide) hc.base.tick
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩, ⟨hs1, hG1, hi1, hmem1, hobs1⟩⟩

theorem fflushEe00Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe00 g c) : ∃ c', Steps c c' ∧ FflushAtEe40 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe00Step_run g c hc
  have hpc := obs_branch_taken_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { base := fflushEntryBase_branch_t g c c1 hc.base
        hs.good hs.tick hs.mem hs.obs
      pc := by
        rwa [show 0x8000ee00#64 + sign_extend (m := 64) (0x0040#13) =
          0x8000ee40#64 from by decide] at hpc
      a3 := obs_branch_taken_other' hs.obs Register.x13 (by decide) hc.a3
      a5 := obs_branch_taken_other' hs.obs Register.x15 (by decide) hc.a5 }⟩

theorem fflushEe00Arm (g : FflushG) :
    Triple (FflushAtEe00 g) (FflushAtEe40 g) := fflushEe00Arm_run g

theorem fflushM1_at_ee40 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000ee40]? = some 0x03#8 ∧
    (fflushM1 g)[0x8000ee41]? = some 0xb5#8 ∧
    (fflushM1 g)[0x8000ee42]? = some 0x05#8 ∧
    (fflushM1 g)[0x8000ee43]? = some 0x0a#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee40 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000ee43 + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEe40_ld_site (σ : MState) (i u : Nat)
    (vminstret v11 : BitVec 64) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000ee40#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hb0 : σ.mem[0x8000ee40]? = some 0x03#8)
    (hb1 : σ.mem[0x8000ee41]? = some 0xb5#8)
    (hb2 : σ.mem[0x8000ee42]? = some 0x05#8)
    (hb3 : σ.mem[0x8000ee43]? = some 0x0a#8)
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x0a0#12)).toNat)
    (hhi : (v11 + sign_extend (m := 64) (0x0a0#12)).toNat + 8 ≤
      0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x0a0#12)).toNat + 8 ≤
        tohostAddr ∨ tohostAddr + 8 ≤
          (v11 + sign_extend (m := 64) (0x0a0#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x0a0#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ'
        (sigmaPost_alu σ (0x8000ee40#64) vminstret Register.x10
          (sign_extend (m := 64)
            (bytesT8 σ.mem
              (v11 + sign_extend (m := 64) (0x0a0#12)).toNat : BitVec (8 * 8)))) := by
  exact stepObs_alu σ i u (0x8000ee40#64) vminstret (0x0a05b503#32)
    (instruction.LOAD (0x0a0#12, regidx.Regidx 0x0b#5,
      regidx.Regidx 0x0a#5, false, 8)) Register.x10
    (sign_extend (m := 64)
      (bytesT8 σ.mem
        (v11 + sign_extend (m := 64) (0x0a0#12)).toNat : BitVec (8 * 8)))
    (0x03#8) (0xb5#8) (0x05#8) (0x0a#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0a05b503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_tot σ (0x8000ee40#64) (0x0a0#12)
      (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x8000ee40#64) Register.x10
        (sign_extend (m := 64)
          (bytesT8 σ.mem
            (v11 + sign_extend (m := 64) (0x0a0#12)).toNat : BitVec (8 * 8))))
      v11 hG
      (rX_bits_x11 _ v11 (by
        rw [get?_afterNextPC σ (0x8000ee40#64) _ (by decide) (by decide)]
        exact hx11))
      (wX_bits_x10 _
        (sign_extend (m := 64)
          (bytesT8 σ.mem
            (v11 + sign_extend (m := 64) (0x0a0#12)).toNat : BitVec (8 * 8))))
      hlo hhi hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe40Step (g : FflushG) (c : Config)
    (vm loaded : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = c.σ.mem
  loaded_eq : loaded = 0#64
  obs : ReadsLikePost c1.σ
    (sigmaPost_alu c.σ (0x8000ee40#64) vm Register.x10 loaded)

theorem fflushEe40Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe40 g c) : ∃ vm loaded c1, FflushEe40Step g c vm loaded c1 := by
  obtain ⟨vm, hmi⟩ := hc.base.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_ee40 g hc.base.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe40_ld_site c.σ c.tick c.steps vm
      (BitVec.ofNat 64 consoleStdout) hc.base.good hc.pc hmi hc.base.a1
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by rwa [hc.base.mem]) (by rwa [hc.base.mem])
      (by decide) (by decide) (by right; decide) (by decide) hc.base.tick
  let loaded := sign_extend (m := 64)
    (bytesT8 c.σ.mem
      (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x0a0#12)).toNat : BitVec (8 * 8))
  have heq : loaded = 0#64 := by
    unfold loaded
    have hlock : read64 c.σ.mem (consoleStdout + 160) = some 0 := by
      rw [hc.base.mem, fflushM1_eq, read64_writeMap8_disjoint]
      · exact hc.base.ok.console.lock
      · left
        rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
          fflush_slot_toNat g.sp hc.base.ok.stack 24 (by decide)]
        have hn := hc.base.ok.stack.nested.console
        rw [fflush_spE_toNat g.sp hc.base.ok.stack] at hn
        dsimp [consoleStdout] at *
        omega
    have hp := fflush_lpins8_zero hlock
    have haddr : (BitVec.ofNat 64 consoleStdout +
        sign_extend (m := 64) (0x0a0#12)).toNat = consoleStdout + 160 := by decide
    rw [haddr, bytesT8_of_lpins8 hp]
    decide
  exact ⟨vm, loaded, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1, heq, hobs1⟩⟩

theorem fflushEe40Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe40 g c) : ∃ c', Steps c c' ∧ FflushAtEe44 g c' := by
  obtain ⟨vm, loaded, c1, hs⟩ := fflushEe40Step_run g c hc
  have hpc := obs_alu_pc hs.obs
  have ha0 := obs_gpr_rd 10 (by decide) (by decide) loaded hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushPersist := fflushPersist_alu10 g c c1 hc.base.toPersist
        hs.good hs.tick hs.obs
      mem := hs.mem.trans hc.base.mem
      pc := by
        rwa [show BitVec.addInt (0x8000ee40#64) 4 = 0x8000ee44#64 from by decide]
          at hpc
      a0 := by rwa [hs.loaded_eq] at ha0
      a1 := obs_alu_other' hs.obs Register.x11 (by decide) hc.base.a1
      a3 := obs_alu_other' hs.obs Register.x13 (by decide) hc.a3
      a4 := obs_alu_other' hs.obs Register.x14 (by decide) hc.base.a4
      a5 := obs_alu_other' hs.obs Register.x15 (by decide) hc.a5
      ra := obs_alu_other' hs.obs Register.x1 (by decide) hc.base.ra
      sp := obs_alu_other' hs.obs Register.x2 (by decide) hc.base.sp }⟩

theorem fflushEe40Arm (g : FflushG) :
    Triple (FflushAtEe40 g) (FflushAtEe44 g) := fflushEe40Arm_run g

theorem fflushM1_at_ee44 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000ee44]? = some 0x23#8 ∧
    (fflushM1 g)[0x8000ee45]? = some 0x34#8 ∧
    (fflushM1 g)[0x8000ee46]? = some 0xe1#8 ∧
    (fflushM1 g)[0x8000ee47]? = some 0x00#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee44 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000ee47 + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEe44_store_site (σ : MState) (i u : Nat)
    (vminstret vsp v14 : BitVec 64) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000ee44#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hb0 : σ.mem[0x8000ee44]? = some 0x23#8)
    (hb1 : σ.mem[0x8000ee45]? = some 0x34#8)
    (hb2 : σ.mem[0x8000ee46]? = some 0xe1#8)
    (hb3 : σ.mem[0x8000ee47]? = some 0x00#8)
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (hhi : (vsp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤
      0x100000000)
    (hwin : tohostAddr + 16 ≤
      (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 σ.mem
        (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v14) ∧
      ReadsLikePost σ' (sigmaPost_store σ (0x8000ee44#64) vminstret
        (writeMap8 σ.mem
          (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v14))) := by
  exact stepObs_store σ i u (0x8000ee44#64) vminstret (0x00e13423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x0e#5,
      regidx.Regidx 0x02#5, 8))
    (writeMap8 σ.mem
      (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v14))
    (0x23#8) (0x34#8) (0xe1#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00e13423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000ee44#64) (0x008#12)
      (regidx.Regidx 0x0e#5) (regidx.Regidx 0x02#5) vsp v14 hG
      (rX_bits_x2 _ vsp (by
        rw [get?_afterNextPC σ (0x8000ee44#64) _ (by decide) (by decide)]
        exact hx2))
      (rX_bits_x14 _ v14 (by
        rw [get?_afterNextPC σ (0x8000ee44#64) _ (by decide) (by decide)]
        exact hx14))
      hlo hhi hwin halign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe44Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = fflushM2 g
  obs : ReadsLikePost c1.σ
    (sigmaPost_store c.σ (0x8000ee44#64) vm (fflushM2 g))

theorem fflushEe44_addr_eq (g : FflushG) (hg : FflushGOk g) :
    (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat =
      (fflushSpE g.sp).toNat + 8 := by
  rw [show sign_extend (m := 64) (0x008#12) = 8#64 by decide,
    fflush_slot_toNat g.sp hg.stack 8 (by decide),
    fflush_spE_toNat g.sp hg.stack]

theorem fflushEe44_lo (g : FflushG) (hg : FflushGOk g) :
    0x80000000 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat := by
  rw [fflushEe44_addr_eq g hg]
  have h := fflush_store0_range g.sp hg.stack
  omega

theorem fflushEe44_hi (g : FflushG) (hg : FflushGOk g) :
    (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤
      0x100000000 := by
  rw [fflushEe44_addr_eq g hg, fflush_spE_toNat g.sp hg.stack]
  have hlo := hg.stack.lo
  have hhi := hg.stack.hi
  omega

theorem fflushEe44_win (g : FflushG) (hg : FflushGOk g) :
    tohostAddr + 16 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat := by
  rw [fflushEe44_addr_eq g hg]
  have h := fflush_store0_range g.sp hg.stack
  omega

theorem fflushEe44_align (g : FflushG) (hg : FflushGOk g) :
    (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0 := by
  rw [fflushEe44_addr_eq g hg]
  have h := fflush_store0_range g.sp hg.stack
  apply Nat.dvd_iff_mod_eq_zero.mp
  exact Nat.dvd_add (Nat.dvd_iff_mod_eq_zero.mpr h.2.2.2) (Nat.dvd_refl 8)

theorem fflushEe44_mem_eq (g : FflushG) :
    writeMap8 (fflushM1 g)
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
      (sdData_val (BitVec.ofNat 64 consoleReent)) = fflushM2 g := rfl

theorem fflushEe44Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe44 g c) : ∃ vm c1, FflushEe44Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_ee44 g hc.ok
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe44_store_site c.σ c.tick c.steps vm (fflushSpE g.sp)
      (BitVec.ofNat 64 consoleReent) hc.good hc.pc hmi hc.sp hc.a4
      (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem])
      (fflushEe44_lo g hc.ok) (fflushEe44_hi g hc.ok)
      (fflushEe44_win g hc.ok) (fflushEe44_align g hc.ok)
      hc.tick
  have hm : writeMap8 c.σ.mem
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
      (sdData_val (BitVec.ofNat 64 consoleReent)) = fflushM2 g := by
    rw [hc.mem]
    exact fflushEe44_mem_eq g
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1.trans hm, by rwa [hm] at hobs1⟩⟩

theorem fflushEe44Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe44 g c) : ∃ c', Steps c c' ∧ FflushAtEe48 g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe44Step_run g c hc
  have hpc := obs_store_pc hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { toFflushPersist := fflushPersist_store g c c1 hc.toFflushPersist
        hs.good hs.tick hs.obs
      mem := hs.mem
      pc := by
        rwa [show BitVec.addInt (0x8000ee44#64) 4 = 0x8000ee48#64 from by decide]
          at hpc
      a0 := obs_store_other' hs.obs Register.x10 (by decide) hc.a0
      a1 := obs_store_other' hs.obs Register.x11 (by decide) hc.a1
      a3 := obs_store_other' hs.obs Register.x13 (by decide) hc.a3
      a4 := obs_store_other' hs.obs Register.x14 (by decide) hc.a4
      a5 := obs_store_other' hs.obs Register.x15 (by decide) hc.a5
      ra := obs_store_other' hs.obs Register.x1 (by decide) hc.ra
      sp := obs_store_other' hs.obs Register.x2 (by decide) hc.sp }⟩

theorem fflushEe44Arm (g : FflushG) :
    Triple (FflushAtEe44 g) (FflushAtEe48 g) := fflushEe44Arm_run g

theorem fflushM1_at_ee48 (g : FflushG) (hg : FflushGOk g) :
    (fflushM1 g)[0x8000ee48]? = some 0x23#8 ∧
    (fflushM1 g)[0x8000ee49]? = some 0x30#8 ∧
    (fflushM1 g)[0x8000ee4a]? = some 0xb1#8 ∧
    (fflushM1 g)[0x8000ee4b]? = some 0x00#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._fflush_r_at_8000ee48 hg.codeF
  rw [fflushM1_eq]
  have hslot : 0x8000ee4b + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hn := hg.stack.nested.htif
    rw [fflush_spE_toNat g.sp hg.stack] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushM2_at_ee48 (g : FflushG) (hg : FflushGOk g) :
    (fflushM2 g)[0x8000ee48]? = some 0x23#8 ∧
    (fflushM2 g)[0x8000ee49]? = some 0x30#8 ∧
    (fflushM2 g)[0x8000ee4a]? = some 0xb1#8 ∧
    (fflushM2 g)[0x8000ee4b]? = some 0x00#8 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM1_at_ee48 g hg
  unfold fflushM2
  have hslot : 0x8000ee4b + 8 ≤
      (fflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat := by
    rw [fflushEe44_addr_eq g hg]
    have hn := hg.stack.nested.htif
    have he := fflush_spE_toNat g.sp hg.stack
    rw [he] at hn
    have ht : tohostAddr = 0x8001ad00 := rfl
    rw [ht] at hn
    omega
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by left; omega)]; exact hb3⟩

theorem fflushEe48_store_site (σ : MState) (i u : Nat)
    (vminstret vsp v11 : BitVec 64) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000ee48#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hb0 : σ.mem[0x8000ee48]? = some 0x23#8)
    (hb1 : σ.mem[0x8000ee49]? = some 0x30#8)
    (hb2 : σ.mem[0x8000ee4a]? = some 0xb1#8)
    (hb3 : σ.mem[0x8000ee4b]? = some 0x00#8)
    (hlo : 0x80000000 ≤ vsp.toNat)
    (hhi : vsp.toNat + 8 ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ vsp.toNat)
    (halign : vsp.toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 σ.mem vsp.toNat (sdData_val v11) ∧
      ReadsLikePost σ' (sigmaPost_store σ (0x8000ee48#64) vminstret
        (writeMap8 σ.mem vsp.toNat (sdData_val v11))) := by
  exact stepObs_store σ i u (0x8000ee48#64) vminstret (0x00b13023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0b#5,
      regidx.Regidx 0x02#5, 8))
    (writeMap8 σ.mem vsp.toNat (sdData_val v11))
    (0x23#8) (0x30#8) (0xb1#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00b13023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by
      simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
        using exec_sd_val σ (0x8000ee48#64) (0x000#12)
          (regidx.Regidx 0x0b#5) (regidx.Regidx 0x02#5) vsp v11 hG
          (rX_bits_x2 _ vsp (by
            rw [get?_afterNextPC σ (0x8000ee48#64) _ (by decide) (by decide)]
            exact hx2))
          (rX_bits_x11 _ v11 (by
            rw [get?_afterNextPC σ (0x8000ee48#64) _ (by decide) (by decide)]
            exact hx11))
          (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
            using hlo)
          (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
            using hhi)
          (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
            using hwin)
          (by simpa [show sign_extend (m := 64) (0x000#12) = 0#64 by decide]
            using halign))
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

structure FflushEe48Step (g : FflushG) (c : Config)
    (vm : BitVec 64) (c1 : Config) : Prop where
  step : Step c c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = fflushAcquireM g
  obs : ReadsLikePost c1.σ
    (sigmaPost_store c.σ (0x8000ee48#64) vm (fflushAcquireM g))

theorem fflushEe48Step_run (g : FflushG) (c : Config)
    (hc : FflushAtEe48 g c) : ∃ vm c1, FflushEe48Step g c vm c1 := by
  obtain ⟨vm, hmi⟩ := hc.minstret
  obtain ⟨hb0, hb1, hb2, hb3⟩ := fflushM2_at_ee48 g hc.ok
  have hrange := fflush_store0_range g.sp hc.ok.stack
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    fflushEe48_store_site c.σ c.tick c.steps vm (fflushSpE g.sp)
      (BitVec.ofNat 64 consoleStdout) hc.good hc.pc hmi hc.sp hc.a1
      (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem]) (by rwa [hc.mem])
      hrange.1 hrange.2.1 hrange.2.2.1 hrange.2.2.2 hc.tick
  have hm : writeMap8 c.σ.mem (fflushSpE g.sp).toNat
      (sdData_val (BitVec.ofNat 64 consoleStdout)) = fflushAcquireM g := by
    rw [hc.mem]
    rfl
  exact ⟨vm, ⟨σ1, i1, c.steps + 1⟩,
    ⟨hs1, hG1, hi1, hmem1.trans hm, by rwa [hm] at hobs1⟩⟩

theorem fflushEe48Arm_run (g : FflushG) (c : Config)
    (hc : FflushAtEe48 g c) : ∃ c', Steps c c' ∧ FflushAtAcquire g c' := by
  obtain ⟨vm, c1, hs⟩ := fflushEe48Step_run g c hc
  have hpc := obs_store_pc hs.obs
  have hp := fflushPersist_store g c c1 hc.toFflushPersist
    hs.good hs.tick hs.obs
  exact ⟨c1, Steps.head hs.step (Steps.refl _),
    { ok := hp.ok
      good := hp.good
      tick := hp.tick
      mem := hs.mem
      pc := by
        rwa [show BitVec.addInt (0x8000ee48#64) 4 = 0x8000ee4c#64 from by decide]
          at hpc
      minstret := hp.minstret
      ra := obs_store_other' hs.obs Register.x1 (by decide) hc.ra
      keep := ⟨
        obs_store_other' hs.obs Register.x10 (by decide) hc.a0,
        obs_store_other' hs.obs Register.x11 (by decide) hc.a1,
        obs_store_other' hs.obs Register.x14 (by decide) hc.a4,
        obs_store_other' hs.obs Register.x2 (by decide) hc.sp,
        hp.gp, hp.s0, hp.sregs⟩
      out := hp.out
      pw := hp.pw
      th := hp.th }⟩

theorem fflushEe48Arm (g : FflushG) :
    Triple (FflushAtEe48 g) (FflushAtAcquire g) := fflushEe48Arm_run g

theorem fflushEntryToEde0 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEde0 g) :=
  Triple.seq (fflushEdccArm g) (fflushEddcArm g)

theorem fflushEntryToEde4 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEde4 g) :=
  Triple.seq (fflushEntryToEde0 g) (fflushEde0Arm g)

theorem fflushEntryToEde8 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEde8 g) :=
  Triple.seq (fflushEntryToEde4 g) (fflushEde4Arm g)

theorem fflushEntryToEdec (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEdec g) :=
  Triple.seq (fflushEntryToEde8 g) (fflushEde8Arm g)

theorem fflushEntryToEdf0 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEdf0 g) :=
  Triple.seq (fflushEntryToEdec g) (fflushEdecArm g)

theorem fflushEntryToEdf4 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEdf4 g) :=
  Triple.seq (fflushEntryToEdf0 g) (fflushEdf0Arm g)

theorem fflushEntryToEdf8 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEdf8 g) :=
  Triple.seq (fflushEntryToEdf4 g) (fflushEdf4Arm g)

theorem fflushEntryToEdfc (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEdfc g) :=
  Triple.seq (fflushEntryToEdf8 g) (fflushEdf8Arm g)

theorem fflushEntryToEe00 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEe00 g) :=
  Triple.seq (fflushEntryToEdfc g) (fflushEdfcArm g)

theorem fflushEntryToEe40 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEe40 g) :=
  Triple.seq (fflushEntryToEe00 g) (fflushEe00Arm g)

theorem fflushEntryToEe44 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEe44 g) :=
  Triple.seq (fflushEntryToEe40 g) (fflushEe40Arm g)

theorem fflushEntryToEe48 (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtEe48 g) :=
  Triple.seq (fflushEntryToEe44 g) (fflushEe44Arm g)

theorem fflushEntryArm (g : FflushG) :
    Triple (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c)
      (FflushAtAcquire g) :=
  Triple.seq (fflushEntryToEe48 g) (fflushEe48Arm g)

theorem fflushPostToEe14 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe14 g) :=
  Triple.seq (fflushPostToEe10 g) (fflushEe10Arm g)

theorem fflushPostToEe18 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe18 g) :=
  Triple.seq (fflushPostToEe14 g) (fflushEe14Arm g)

theorem fflushPostToEe1c (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe1c g) :=
  Triple.seq (fflushPostToEe18 g) (fflushEe18Arm g)

theorem fflushPostToEe20 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe20 g) :=
  Triple.seq (fflushPostToEe1c g) (fflushEe1cArm g)

theorem fflushPostToEe24 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe24 g) :=
  Triple.seq (fflushPostToEe20 g) (fflushEe20Arm g)

theorem fflushPostToEe28 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe28 g) :=
  Triple.seq (fflushPostToEe24 g) (fflushEe24Arm g)

theorem fflushPostToEe2c (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe2c g) :=
  Triple.seq (fflushPostToEe28 g) (fflushEe28Arm g)

theorem fflushPostToEe5c (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe5c g) :=
  Triple.seq (fflushPostToEe2c g) (fflushEe2cArm g)

theorem fflushPostToEe60 (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtEe60 g) :=
  Triple.seq (fflushPostToEe5c g) (fflushEe5cArm g)

theorem fflushPostToRelease (g : FflushG) :
    Triple (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c)
      (FflushAtRelease g) :=
  Triple.seq (fflushPostToEe60 g) (fflushEe60Arm g)

theorem fflushAcquireToSflushPost (g : FflushG) :
    Triple (FflushAtAcquire g)
      (fun c => FflushGOk g ∧ SflushFnPost (fflushSG g) c) :=
  Triple.seq (fflushAcquireReturnArm g)
    (Triple.seq (fflushEe04Arm g) (fflushSflushArm g))

theorem fflushAcquireToRelease (g : FflushG) :
    Triple (FflushAtAcquire g) (FflushAtRelease g) :=
  Triple.seq (fflushAcquireToSflushPost g) (fflushPostToRelease g)

theorem fflushReleaseToPost (g : FflushG) :
    Triple (FflushAtRelease g) (FflushFnPost g) :=
  Triple.seq (fflushReleaseArm_ok g)
    (Triple.seq (fflushReleaseToEe68 g) (fflushEpilogueArm g))

/-- Exact `_fflush_r` success-route summary: acquire, `__sflush_r`, release,
and restored return to the caller. -/
theorem fflush_summary (g : FflushG) :
    FnSummary 0x8000edcc#64 (FflushFnPre g) (FflushFnPost g) := by
  refine ⟨?_⟩
  exact Triple.seq (fflushEntryArm g)
    (Triple.seq (fflushAcquireToRelease g) (fflushReleaseToPost g))

#print axioms fflush_summary

def fflushEe68Lds (g : FflushG) : List (List (BitVec 8)) :=
  [flushBytes8 (0#64), flushBytes8 g.ra]

/-
theorem fflushEe68_facts (g : FflushG) (hg : FflushGOk g) :
    ChainFacts (fflushReleaseM g) (fflushReleaseM g)
      (fflush_rXee68L (fflushSpE g.sp)) (fflushEe68Lds g)
      fflush_rXee68Seg := by
  chain_facts hg.codeF_release with "Vsa.Sim.Code._fflush_r_at_"
  · exact ⟨fflush_store0_range g.sp hg.stack,
      fflush_lpins8_of_pin (fflushRelease_slot0_pin g)⟩
  · refine ⟨?_, fflush_lpins8_of_pin (fflushRelease_slot24_pin g hg)⟩
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 by decide,
      fflush_slot_toNat g.sp hg.stack 24 (by decide)]
    have hs := hg.stack
    rw [fflush_spE_toNat g.sp hs]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have hn := hs.nested.htif
    have hh := hs.hi
    have ha := hs.align
    rw [fflush_spE_toNat g.sp hs] at hn
    exact ⟨by omega, by omega, by omega, by omega⟩
  · show (BitVec.update (g.ra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [show BitVec.update (g.ra + sign_extend (m := 64) (0x000#12)) 0 0#1 = g.ra by
      apply BitVec.eq_of_toNat_eq
      have ha := hg.ra_align
      omega]
    exact hg.ra_align
-/

end Vsa.Sim

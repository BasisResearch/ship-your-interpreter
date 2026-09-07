import Vsa.Sim.rows.FnSflushR
import Vsa.Sim.rows.FnSwriteFold
import Vsa.Sim.ConsoleStream
import Vsa.Sim.ChainFactsTac

/-!
# Concrete one-byte `__sflush_r` route

The initialized stdout path is finite.  The FILE has `__SWR | __SNBF`, one
pending byte, and `__swrite` as its callback.  This module joins exactly the
five reflected blocks before the callback.  It deliberately does not use the
unrelated `__sfvwrite_r` summary: this binary calls `__swrite` directly here.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

def flushBytes8 (v : BitVec 64) : List (BitVec 8) :=
  [(sdData_val v).extractLsb' 0 8, (sdData_val v).extractLsb' 8 8,
   (sdData_val v).extractLsb' 16 8, (sdData_val v).extractLsb' 24 8,
   (sdData_val v).extractLsb' 32 8, (sdData_val v).extractLsb' 40 8,
   (sdData_val v).extractLsb' 48 8, (sdData_val v).extractLsb' 56 8]

theorem flushBytes8_val (v : BitVec 64) :
    bytesVal MKind.ld (flushBytes8 v) = v :=
  sext_reassemble v
    ((sdData_val v).extractLsb' 0 8) ((sdData_val v).extractLsb' 8 8)
    ((sdData_val v).extractLsb' 16 8) ((sdData_val v).extractLsb' 24 8)
    ((sdData_val v).extractLsb' 32 8) ((sdData_val v).extractLsb' 40 8)
    ((sdData_val v).extractLsb' 48 8) ((sdData_val v).extractLsb' 56 8)
    rfl rfl rfl rfl rfl rfl rfl rfl

/-- Reflected prefix through the indirect `jalr __swrite`. -/
def sflushConsolePrefixSeg : List BBlock :=
  sflush_rXeb70TSeg ++ sflush_rXecb4FSeg ++ sflush_rXecc0TSeg ++
  sflush_rXece0TSeg ++ sflush_rXecf4Seg

def sflushConsoleL (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  (9, s1) :: (18, s2) ::
    sflush_rXeb70TL (BitVec.ofNat 64 consoleStdout) sp s0 s3 ra
      (BitVec.ofNat 64 consoleReent)

def sflushConsoleLds : List (List (BitVec 8)) :=
  [[0x0a#8, 0x20#8], flushBytes8 (BitVec.ofNat 64 consoleBuf),
   flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
   flushBytes8 (BitVec.ofNat 64 consoleSwrite),
   flushBytes8 (BitVec.ofNat 64 consoleStdout)]

def sflushL1 (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(19, BitVec.ofNat 64 consoleReent), (8, BitVec.ofNat 64 consoleStdout),
   (15, 8#64), (2, sp + sign_extend (m := 64) (0xfd0#12)),
   (14, 0x200a#64), (9, s1), (18, s2),
   (11, BitVec.ofNat 64 consoleStdout), (1, ra), (10, BitVec.ofNat 64 consoleReent)]

def sflushL2 (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(18, BitVec.ofNat 64 consoleBuf), (19, BitVec.ofNat 64 consoleReent),
   (8, BitVec.ofNat 64 consoleStdout), (15, 8#64),
   (2, sp + sign_extend (m := 64) (0xfd0#12)),
   (14, 0x200a#64), (9, s1), (11, BitVec.ofNat 64 consoleStdout),
   (1, ra), (10, BitVec.ofNat 64 consoleReent)]

def sflushL3 (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(15, 0#64), (9, 1#64), (14, 2#64), (18, BitVec.ofNat 64 consoleBuf),
   (19, BitVec.ofNat 64 consoleReent), (8, BitVec.ofNat 64 consoleStdout),
   (2, sp + sign_extend (m := 64) (0xfd0#12)),
   (11, BitVec.ofNat 64 consoleStdout), (1, ra),
   (10, BitVec.ofNat 64 consoleReent)]

structure SflushStackOK (sp : BitVec 64) : Prop where
  htif : tohostAddr + 16 ≤ sp.toNat - 48
  console : consoleStdout + 184 ≤ sp.toNat - 48
  callbackHtif : tohostAddr + 16 ≤ sp.toNat - 96
  callbackErrno : wrErrnoAddr + 4 ≤ sp.toNat - 96
  callbackConsole : consoleStdout + 184 ≤ sp.toNat - 96
  hi : sp.toNat ≤ 0x100000000
  align : sp.toNat % 8 = 0

/-- Ghost state for the concrete successful one-byte `__sflush_r` route. -/
structure SflushG where
  ch : BitVec 8
  sp : BitVec 64
  ra : BitVec 64
  s0 : BitVec 64
  sv : SRegs
  m0 : Mem
  out0 : Array String

/-- Exact static and entry-memory facts needed by the flush/callback chain. -/
structure SflushGOk (g : SflushG) : Prop where
  stack : SflushStackOK g.sp
  ra_align : g.ra.toNat % 4 = 0
  console : ConsoleFlushState g.m0 g.ch
  codeF : Vsa.Sim.Code.__sflush_rLoaded g.m0
  codeW : Vsa.Sim.Code._writeLoaded g.m0
  codeR : Vsa.Sim.Code._write_rLoaded g.m0
  codeS : Vsa.Sim.Code.__swriteLoaded g.m0

def sflushSpE (sp : BitVec 64) : BitVec 64 :=
  sp + sign_extend (m := 64) (0xfd0#12)

theorem sflush_spE_toNat (sp : BitVec 64) (hs : SflushStackOK sp) :
    (sflushSpE sp).toNat = sp.toNat - 48 := by
  refine ptr_sub_toNat sp (0xfd0#12) 48 sext_fd0_toNat ?_
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hs.htif
  omega

theorem sflush_slot_toNat (sp : BitVec 64) (hs : SflushStackOK sp)
    (off : Nat) (hi : off < 2048) (hoff : off ≤ 48) :
    (sflushSpE sp + BitVec.ofNat 64 off).toNat = sp.toNat - 48 + off := by
  have hsp := sflush_spE_toNat sp hs
  have hlt : (sflushSpE sp).toNat + off < 2 ^ 64 := by
    have := hs.hi
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), hsp]
  omega

theorem sflushConsolePrefix_facts
    (mc m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64)
    (hc : ConsoleFlushState m ch)
    (hs : SflushStackOK sp)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ChainFacts mc m (sflushConsoleL sp s0 s1 s2 s3 ra) sflushConsoleLds
      sflush_rXeb70TSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sflush_r_at_"
  · -- lh flags
    have ha : ((BitVec.ofNat 64 consoleStdout : BitVec 64) +
        sign_extend (m := 64) (0x010#12)).toNat = consoleStdout + 16 := by decide
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · change 0x80000000 ≤ ((BitVec.ofNat 64 consoleStdout : BitVec 64) +
        sign_extend (m := 64) (0x010#12)).toNat
      rw [ha]; decide
    · change ((BitVec.ofNat 64 consoleStdout : BitVec 64) +
        sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ 0x100000000
      rw [ha]; decide
    · change ((BitVec.ofNat 64 consoleStdout : BitVec 64) +
          sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ ((BitVec.ofNat 64 consoleStdout : BitVec 64) +
          sign_extend (m := 64) (0x010#12)).toNat
      rw [ha]; right; decide
    · change (m[((BitVec.ofNat 64 consoleStdout : BitVec 64) +
        sign_extend (m := 64) (0x010#12)).toNat]?).getD 0 = 0x0a#8
      rw [ha]; exact lpin_of_present hc.flag0
    · change (m[((BitVec.ofNat 64 consoleStdout : BitVec 64) +
        sign_extend (m := 64) (0x010#12)).toNat + 1]?).getD 0 = 0x20#8
      rw [ha, show consoleStdout + 16 + 1 = consoleStdout + 17 by omega]
      exact lpin_of_present hc.flag1
  · -- sd s0,32(sp-48)
    show 0x80000000 ≤ (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0
    have ha : (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat =
        sp.toNat - 16 := by
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hs.htif
      rw [show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
        sflush_slot_toNat sp hs 32 (by decide) (by decide)]
      omega
    rw [ha]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif; have := hs.hi; have := hs.align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd s3,8(sp-48)
    show 0x80000000 ≤ (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0
    have ha : (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat =
        sp.toNat - 40 := by
      rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
        sflush_slot_toNat sp hs 8 (by decide) (by decide)]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hs.htif
      omega
    rw [ha]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif; have := hs.hi; have := hs.align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd ra,40(sp-48)
    show 0x80000000 ≤ (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0
    have ha : (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat =
        sp.toNat - 8 := by
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hs.htif
      rw [show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
        sflush_slot_toNat sp hs 40 (by decide) (by decide)]
      omega
    rw [ha]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif; have := hs.hi; have := hs.align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- `0x200a & 8 != 0`
    show (bytesVal MKind.lh [0x0a#8, 0x20#8] &&&
      sign_extend (m := 64) (0x008#12) != 0#64) = true
    decide

def sflushEntryLog (sp s0 s3 ra : BitVec 64) : List WEntry :=
  [((sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat, 8, s0),
   ((sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat, 8, s3),
   ((sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat, 8, ra)]

theorem sflushEntryLog_eq (sp s0 s1 s2 s3 ra : BitVec 64) :
    (evalBlocks sflush_rXeb70TSeg
      (SegEvalState.init (sflushConsoleL sp s0 s1 s2 s3 ra) sflushConsoleLds)).log =
      sflushEntryLog sp s0 s3 ra := rfl

def sflushM1 (m : Mem) (sp s0 s3 ra : BitVec 64) : Mem :=
  writeLog m (sflushEntryLog sp s0 s3 ra)

theorem sflushM1_console_agree (m : Mem) (sp s0 s3 ra : BitVec 64)
    (hs : SflushStackOK sp) (a : Nat) (ha : ConsoleFoot a) :
    (sflushM1 m sp s0 s3 ra)[a]? = m[a]? := by
  have hbelow : a < sp.toNat - 48 := by
    rcases ha with ha | ha | ha | rfl
    · have hbound : a < consoleStdout + 184 := by
        dsimp [consoleImpurePtrAddr, consoleStdout] at *
        omega
      exact Nat.lt_of_lt_of_le hbound hs.console
    · have hbound : a < consoleStdout + 184 := by
        dsimp [consoleReent, consoleStdout] at *
        omega
      exact Nat.lt_of_lt_of_le hbound hs.console
    · exact Nat.lt_of_lt_of_le ha.2 hs.console
    · have hbound : consoleBuf < consoleStdout + 184 := by
        dsimp [consoleBuf, consoleStdout]
        omega
      exact Nat.lt_of_lt_of_le hbound hs.console
  have h8 : (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat =
      sp.toNat - 40 := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
      sflush_slot_toNat sp hs 8 (by decide) (by decide)]
    omega
  have h20 : (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat =
      sp.toNat - 16 := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    rw [show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
      sflush_slot_toNat sp hs 32 (by decide) (by decide)]
    omega
  have h28 : (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat =
      sp.toNat - 8 := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    rw [show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
      sflush_slot_toNat sp hs 40 (by decide) (by decide)]
    omega
  unfold sflushM1 sflushEntryLog writeLog
  simp only [List.foldl_cons, List.foldl_nil, applyW]
  rw [getElem_writeMap8_disjoint _ _ a _ (by rw [h28]; omega)]
  rw [getElem_writeMap8_disjoint _ _ a _ (by rw [h8]; omega)]
  exact getElem_writeMap8_disjoint _ _ a _ (by rw [h20]; omega)

theorem sflushM1_console (m : Mem) (sp s0 s3 ra : BitVec 64)
    (hs : SflushStackOK sp) (hc : ConsoleFlushState m ch) :
    ConsoleFlushState (sflushM1 m sp s0 s3 ra) ch := by
  exact ConsoleFlushState.of_agree
    (sflushM1_console_agree m sp s0 s3 ra hs) hc

private theorem lpins8_consoleBuf {m : Mem} {a : Nat}
    (h : read64 m a = some consoleBuf) :
    LPins8 m a (flushBytes8 (BitVec.ofNat 64 consoleBuf)) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
    h0, h1, h2, h3, h4, h5, h6, h7, hv⟩ :=
    read64_bytes m a consoleBuf h
  have hb0 := b0.isLt; have hb1 := b1.isLt; have hb2 := b2.isLt
  have hb3 := b3.isLt; have hb4 := b4.isLt; have hb5 := b5.isLt
  have hb6 := b6.isLt; have hb7 := b7.isLt
  dsimp [consoleBuf] at hv
  have e0 : b0 = 0x97#8 := by apply BitVec.eq_of_toNat_eq; change b0.toNat = 151; omega
  have e1 : b1 = 0xbb#8 := by apply BitVec.eq_of_toNat_eq; change b1.toNat = 187; omega
  have e2 : b2 = 0x01#8 := by apply BitVec.eq_of_toNat_eq; change b2.toNat = 1; omega
  have e3 : b3 = 0x80#8 := by apply BitVec.eq_of_toNat_eq; change b3.toNat = 128; omega
  have e4 : b4 = 0x00#8 := by apply BitVec.eq_of_toNat_eq; change b4.toNat = 0; omega
  have e5 : b5 = 0x00#8 := by apply BitVec.eq_of_toNat_eq; change b5.toNat = 0; omega
  have e6 : b6 = 0x00#8 := by apply BitVec.eq_of_toNat_eq; change b6.toNat = 0; omega
  have e7 : b7 = 0x00#8 := by apply BitVec.eq_of_toNat_eq; change b7.toNat = 0; omega
  subst b0; subst b1; subst b2; subst b3; subst b4; subst b5; subst b6; subst b7
  change LPins8 m a
    [0x97#8, 0xbb#8, 0x01#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]
  unfold LPins8
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨lpin_of_present h0, lpin_of_present h1, lpin_of_present h2,
    lpin_of_present h3, lpin_of_present h4, lpin_of_present h5,
    lpin_of_present h6, lpin_of_present h7⟩

theorem sflushLoaded_of_agree (m m' : Mem)
    (hagree : ∀ a, 0x8000eb70 ≤ a → a < 0x8000edcc → m'[a]? = m[a]?)
    (hc : Vsa.Sim.Code.__sflush_rLoaded m) :
    Vsa.Sim.Code.__sflush_rLoaded m' := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.__sflush_rChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk4] at c4 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk5] at c5 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk6] at c6 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk7] at c7 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk8] at c8 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.__sflush_rChunk9] at c9 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])

theorem sflushLoaded_writeMap8 (m : Mem) (a : Nat) (d : BitVec 64)
    (hdis : a + 8 ≤ 0x8000eb70 ∨ 0x8000edcc ≤ a)
    (hc : Vsa.Sim.Code.__sflush_rLoaded m) :
    Vsa.Sim.Code.__sflush_rLoaded (writeMap8 m a d) :=
  sflushLoaded_of_agree m _
    (fun k hlo hhi => getElem_writeMap8_disjoint m a k d (by
      rcases hdis with h | h <;> omega)) hc

theorem lpins8_writeMap8_disjoint {m : Mem} {base : Nat} {bs : List (BitVec 8)}
    (a : Nat) (d : BitVec 64)
    (hdis : base + 8 ≤ a ∨ a + 8 ≤ base)
    (hp : LPins8 m base bs) : LPins8 (writeMap8 m a d) base bs := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := hp
  exact ⟨by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p3,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p4,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p5,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p6,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p7⟩

theorem sflushM1_code (m : Mem) (sp s0 s3 ra : BitVec 64)
    (hs : SflushStackOK sp) (hc : Vsa.Sim.Code.__sflush_rLoaded m) :
    Vsa.Sim.Code.__sflush_rLoaded (sflushM1 m sp s0 s3 ra) := by
  have hsp48 : 48 ≤ sp.toNat := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    omega
  unfold sflushM1 sflushEntryLog writeLog
  simp only [List.foldl_cons, List.foldl_nil, applyW]
  apply sflushLoaded_writeMap8
  · right
    rw [show (sflushSpE sp + sign_extend (m := 64) (0x028#12)).toNat =
      sp.toNat - 8 by
        rw [show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
          sflush_slot_toNat sp hs 40 (by decide) (by decide)]
        omega]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    omega
  · apply sflushLoaded_writeMap8
    · right
      rw [show (sflushSpE sp + sign_extend (m := 64) (0x008#12)).toNat =
        sp.toNat - 40 by
          rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
            sflush_slot_toNat sp hs 8 (by decide) (by decide)]
          omega]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hs.htif
      omega
    · apply sflushLoaded_writeMap8
      · right
        rw [show (sflushSpE sp + sign_extend (m := 64) (0x020#12)).toNat =
          sp.toNat - 16 by
            rw [show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
              sflush_slot_toNat sp hs 32 (by decide) (by decide)]
            omega]
        have ht : tohostAddr = 0x8001ad00 := rfl
        have := hs.htif
        omega
      · exact hc

theorem sflushEcb4_load_addr (sp s2 : BitVec 64) (bs : List (BitVec 8)) :
    eaddrM (mkLine 0x8000ecb8#64 0x0185b903#32)
      (stepGM (mkLine 0x8000ecb4#64 0x01213823#32)
        (sflush_rXecb4FL s2 (sflushSpE sp) (BitVec.ofNat 64 consoleStdout)) bs) =
    (BitVec.ofNat 64 consoleStdout : BitVec 64) +
      sign_extend (m := 64) (0x018#12) := rfl

theorem sflushEcb4_store_mem (m : Mem) (sp s2 : BitVec 64) :
    stepMemM m (mkLine 0x8000ecb4#64 0x01213823#32)
      (sflush_rXecb4FL s2 (sflushSpE sp) (BitVec.ofNat 64 consoleStdout)) =
    writeMap8 m
      (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat
      (sdData_val s2) := rfl

theorem sflushEcb4_facts (mc m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64)
    (hs : SflushStackOK sp) (hc : ConsoleFlushState m ch)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ChainFacts mc m (sflushL1 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 consoleBuf),
       flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] sflush_rXecb4FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sflush_r_at_"
  · -- sd s2,16(spE)
    show 0x80000000 ≤ (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0
    rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      sflush_slot_toNat sp hs 16 (by decide) (by decide)]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif; have := hs.hi; have := hs.align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- ld s2,24(stdout), after the disjoint spill
    have ha : ((BitVec.ofNat 64 consoleStdout : BitVec 64) +
        sign_extend (m := 64) (0x018#12)).toNat = consoleStdout + 24 := by decide
    have hloadAddr :
        eaddrM (mkLine 0x8000ecb8#64 0x0185b903#32)
          (stepGM (mkLine 0x8000ecb4#64 0x01213823#32)
            (sflushL1 sp s0 s1 s2 s3 ra)
            ([flushBytes8 (BitVec.ofNat 64 consoleBuf),
              flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
              flushBytes8 (BitVec.ofNat 64 consoleSwrite),
              flushBytes8 (BitVec.ofNat 64 consoleStdout)].headD [])) =
          (BitVec.ofNat 64 consoleStdout : BitVec 64) +
            sign_extend (m := 64) (0x018#12) := rfl
    have hstoreMem :
        stepMemM m (mkLine 0x8000ecb4#64 0x01213823#32)
          (sflushL1 sp s0 s1 s2 s3 ra) =
          writeMap8 m
            (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat
            (sdData_val s2) := rfl
    unfold MemFacts
    rw [hloadAddr]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha]; decide
    · rw [ha]; decide
    · rw [ha]; right; decide
    · rw [hstoreMem, ha]
      change LPins8 _ _ (flushBytes8 (BitVec.ofNat 64 consoleBuf))
      refine lpins8_writeMap8_disjoint _ _ ?_ (lpins8_consoleBuf hc.base)
      have hsp48 : 48 ≤ sp.toNat := by
        have ht : tohostAddr = 0x8001ad00 := rfl
        have := hs.htif
        omega
      rw [show (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat =
        sp.toNat - 32 by
          rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
            sflush_slot_toNat sp hs 16 (by decide) (by decide)]
          omega]
      have := hs.console
      omega
  · show (bytesVal MKind.ld (flushBytes8 (BitVec.ofNat 64 consoleBuf)) == 0#64) = false
    rw [flushBytes8_val]
    decide

def sflushM2 (m : Mem) (sp s2 : BitVec 64) : Mem :=
  writeMap8 m
    (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat
    (sdData_val s2)

theorem sflushEcb4_log (sp s2 : BitVec 64) :
    (evalBlocks sflush_rXecb4FSeg
      (SegEvalState.init
        (sflush_rXecb4FL s2 (sflushSpE sp) (BitVec.ofNat 64 consoleStdout))
        [flushBytes8 (BitVec.ofNat 64 consoleBuf)])).log =
    [((sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat, 8, s2)] := rfl

theorem sflushM2_console (m : Mem) (sp s2 : BitVec 64)
    (hs : SflushStackOK sp) (hc : ConsoleFlushState m ch) :
    ConsoleFlushState (sflushM2 m sp s2) ch := by
  apply ConsoleFlushState.of_agree _ hc
  intro a ha
  have hsp48 : 48 ≤ sp.toNat := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    omega
  have haddr : (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat =
      sp.toNat - 32 := by
    rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      sflush_slot_toNat sp hs 16 (by decide) (by decide)]
    omega
  have hm2 : sflushM2 m sp s2 = writeMap8 m (sp.toNat - 32) (sdData_val s2) := by
    unfold sflushM2
    rw [haddr]
  rw [hm2]
  apply getElem_writeMap8_disjoint
  clear haddr hm2
  have hcon : 0x8001bb20 + 184 ≤ sp.toNat - 48 := by
    simpa [consoleStdout] using hs.console
  rcases ha with ha | ha | ha | rfl
  · left
    dsimp [consoleImpurePtrAddr, consoleStdout] at *
    omega
  · left
    dsimp [consoleReent, consoleStdout] at *
    omega
  · left
    dsimp [consoleStdout] at ha
    omega
  · left
    dsimp [consoleBuf, consoleStdout] at *
    omega

theorem sflushM2_code (m : Mem) (sp s2 : BitVec 64)
    (hs : SflushStackOK sp) (hc : Vsa.Sim.Code.__sflush_rLoaded m) :
    Vsa.Sim.Code.__sflush_rLoaded (sflushM2 m sp s2) := by
  unfold sflushM2
  apply sflushLoaded_writeMap8
  · right
    have hsp48 : 48 ≤ sp.toNat := by
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hs.htif
      omega
    rw [show (sflushSpE sp + sign_extend (m := 64) (0x010#12)).toNat =
      sp.toNat - 32 by
        rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
          sflush_slot_toNat sp hs 16 (by decide) (by decide)]
        omega]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    omega
  · exact hc

private theorem lpins8_consoleBufNext {m : Mem} {a : Nat}
    (h : read64 m a = some (consoleBuf + 1)) :
    LPins8 m a (flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1))) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
    h0, h1, h2, h3, h4, h5, h6, h7, hv⟩ :=
    read64_bytes m a (consoleBuf + 1) h
  have hb0 := b0.isLt; have hb1 := b1.isLt; have hb2 := b2.isLt
  have hb3 := b3.isLt; have hb4 := b4.isLt; have hb5 := b5.isLt
  have hb6 := b6.isLt; have hb7 := b7.isLt
  dsimp [consoleBuf] at hv
  have e0 : b0 = 0x98#8 := by apply BitVec.eq_of_toNat_eq; change b0.toNat = 152; omega
  have e1 : b1 = 0xbb#8 := by apply BitVec.eq_of_toNat_eq; change b1.toNat = 187; omega
  have e2 : b2 = 0x01#8 := by apply BitVec.eq_of_toNat_eq; change b2.toNat = 1; omega
  have e3 : b3 = 0x80#8 := by apply BitVec.eq_of_toNat_eq; change b3.toNat = 128; omega
  have e4 : b4 = 0x00#8 := by apply BitVec.eq_of_toNat_eq; change b4.toNat = 0; omega
  have e5 : b5 = 0x00#8 := by apply BitVec.eq_of_toNat_eq; change b5.toNat = 0; omega
  have e6 : b6 = 0x00#8 := by apply BitVec.eq_of_toNat_eq; change b6.toNat = 0; omega
  have e7 : b7 = 0x00#8 := by apply BitVec.eq_of_toNat_eq; change b7.toNat = 0; omega
  subst b0; subst b1; subst b2; subst b3; subst b4; subst b5; subst b6; subst b7
  change LPins8 m a
    [0x98#8, 0xbb#8, 0x01#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]
  unfold LPins8
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨lpin_of_present h0, lpin_of_present h1, lpin_of_present h2,
    lpin_of_present h3, lpin_of_present h4, lpin_of_present h5,
    lpin_of_present h6, lpin_of_present h7⟩

private theorem lpins8_of_read64_explicit {m : Mem} {a p : Nat}
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

private theorem lpins8_consoleSwrite {m : Mem} {a : Nat}
    (h : read64 m a = some consoleSwrite) :
    LPins8 m a [0xd4#8, 0xef#8, 0x00#8, 0x80#8, 0#8, 0#8, 0#8, 0#8] := by
  apply lpins8_of_read64_explicit _ _ _ _ _ _ _ _ h
  decide

private theorem lpins8_consoleStdout {m : Mem} {a : Nat}
    (h : read64 m a = some consoleStdout) :
    LPins8 m a [0x20#8, 0xbb#8, 0x01#8, 0x80#8, 0#8, 0#8, 0#8, 0#8] := by
  apply lpins8_of_read64_explicit _ _ _ _ _ _ _ _ h
  decide

def sflushEcc0L (sp s1 : BitVec 64) : GRegs :=
  sflush_rXecc0TL s1 (sflushSpE sp) (BitVec.ofNat 64 consoleStdout)
    (bytesVal MKind.lh [0x0a#8, 0x20#8]) (BitVec.ofNat 64 consoleBuf)

theorem sflushEcc0_load_addr (sp s1 : BitVec 64) (bs : List (BitVec 8)) :
    eaddrM (mkLine 0x8000ecc4#64 0x0005b483#32)
      (stepGM (mkLine 0x8000ecc0#64 0x00913c23#32)
        (sflushEcc0L sp s1) bs) =
    (BitVec.ofNat 64 consoleStdout : BitVec 64) := rfl

theorem sflushEcc0_store_mem (m : Mem) (sp s1 : BitVec 64) :
    stepMemM m (mkLine 0x8000ecc0#64 0x00913c23#32) (sflushEcc0L sp s1) =
    writeMap8 m
      (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat
      (sdData_val s1) := rfl

theorem sflushEcc0_facts (mc m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64)
    (hs : SflushStackOK sp) (hc : ConsoleFlushState m ch)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ChainFacts mc m (sflushL2 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] sflush_rXecc0TSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sflush_r_at_"
  · -- sd s1,24(spE)
    show 0x80000000 ≤ (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat sp hs 24 (by decide) (by decide)]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif; have := hs.hi; have := hs.align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- ld cursor,0(stdout), after disjoint spill
    have hloadAddr :
        eaddrM (mkLine 0x8000ecc4#64 0x0005b483#32)
          (stepGM (mkLine 0x8000ecc0#64 0x00913c23#32)
            (sflushL2 sp s0 s1 s2 s3 ra)
            ([flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
              flushBytes8 (BitVec.ofNat 64 consoleSwrite),
              flushBytes8 (BitVec.ofNat 64 consoleStdout)].headD [])) =
          (BitVec.ofNat 64 consoleStdout : BitVec 64) := rfl
    have hstoreMem :
        stepMemM m (mkLine 0x8000ecc0#64 0x00913c23#32)
          (sflushL2 sp s0 s1 s2 s3 ra) =
          writeMap8 m
            (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat
            (sdData_val s1) := rfl
    unfold MemFacts
    rw [hloadAddr, hstoreMem]
    refine ⟨⟨by decide, by decide, by right; decide⟩, ?_⟩
    change LPins8 _ consoleStdout
      (flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)))
    refine lpins8_writeMap8_disjoint _ _ ?_ (lpins8_consoleBufNext hc.cursor)
    have hsp48 : 48 ≤ sp.toNat := by
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hs.htif
      omega
    rw [show (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat =
      sp.toNat - 24 by
        rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
          sflush_slot_toNat sp hs 24 (by decide) (by decide)]
        omega]
    have hcon : consoleStdout + 184 ≤ sp.toNat - 48 := hs.console
    omega
  · -- sd base,0(stdout)
    unfold MemFacts
    change 0x80000000 ≤ consoleStdout ∧
      consoleStdout + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ consoleStdout ∧ consoleStdout % 8 = 0
    decide
  · -- `(0x200a & 3) != 0`
    show (bytesVal MKind.lh [0x0a#8, 0x20#8] &&&
      sign_extend (m := 64) (0x003#12) != 0#64) = true
    decide

def sflushEce0L : GRegs :=
  sflush_rXece0TL 0#64 (BitVec.ofNat 64 consoleStdout) 1#64

theorem sflushEce0_facts (mc m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ChainFacts mc m (sflushL3 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] sflush_rXece0TSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sflush_r_at_"
  · unfold MemFacts
    change 0x80000000 ≤ consoleStdout + 12 ∧
      consoleStdout + 12 + 4 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ consoleStdout + 12 ∧
      (consoleStdout + 12) % 4 = 0
    decide
  · change guardB bop.BLT (0#64) (1#64) = true
    decide

def sflushM3 (m : Mem) (sp s1 : BitVec 64) : Mem :=
  writeMap8
    (writeMap8 m
      (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat
      (sdData_val s1))
    consoleStdout (sdData_val (BitVec.ofNat 64 consoleBuf))

def sflushM4 (m : Mem) (sp s1 : BitVec 64) : Mem :=
  writeMap4 (sflushM3 m sp s1)
    (consoleStdout + 12) (swData (0#64))

theorem sflushStack24_console (m : Mem) (sp s1 : BitVec 64)
    (hs : SflushStackOK sp) (hc : ConsoleFlushState m ch) :
    ConsoleFlushState
      (writeMap8 m
        (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat
        (sdData_val s1)) ch := by
  apply ConsoleFlushState.of_agree _ hc
  intro a ha
  apply getElem_writeMap8_disjoint
  have hsp48 : 48 ≤ sp.toNat := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hs.htif
    omega
  have haddr : (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat =
      sp.toNat - 24 := by
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat sp hs 24 (by decide) (by decide)]
    omega
  have hcon : 0x8001bb20 + 184 ≤ sp.toNat - 48 := by
    simpa [consoleStdout] using hs.console
  rcases ha with ha | ha | ha | rfl
  · left; rw [haddr]
    dsimp [consoleImpurePtrAddr] at ha
    omega
  · left; rw [haddr]
    dsimp [consoleReent] at ha
    omega
  · left; rw [haddr]
    dsimp [consoleStdout] at ha
    omega
  · left; rw [haddr]
    dsimp [consoleBuf]
    omega

theorem sflushM4_console (m : Mem) (sp s1 : BitVec 64)
    (hs : SflushStackOK sp) (hc : ConsoleFlushState m ch) :
    ConsoleStream (sflushM4 m sp s1) := by
  change ConsoleStream
    (closeConsoleFlush
      (writeMap8 m
        (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat
        (sdData_val s1)))
  exact (sflushStack24_console m sp s1 hs hc).close

theorem sflushLoaded_writeMap4 (m : Mem) (a : Nat) (d : BitVec 32)
    (hdis : a + 4 ≤ 0x8000eb70 ∨ 0x8000edcc ≤ a)
    (hc : Vsa.Sim.Code.__sflush_rLoaded m) :
    Vsa.Sim.Code.__sflush_rLoaded (writeMap4 m a d) :=
  sflushLoaded_of_agree m _
    (fun k hlo hhi => getElem_writeMap4_disjoint m a k d (by
      rcases hdis with h | h <;> omega)) hc

theorem sflushM4_code (m : Mem) (sp s1 : BitVec 64)
    (hs : SflushStackOK sp) (hc : Vsa.Sim.Code.__sflush_rLoaded m) :
    Vsa.Sim.Code.__sflush_rLoaded (sflushM4 m sp s1) := by
  unfold sflushM4
  apply sflushLoaded_writeMap4
  · right; decide
  · apply sflushLoaded_writeMap8
    · right; decide
    · apply sflushLoaded_writeMap8
      · right
        have hsp48 : 48 ≤ sp.toNat := by
          have ht : tohostAddr = 0x8001ad00 := rfl
          have := hs.htif
          omega
        rw [show (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat =
          sp.toNat - 24 by
            rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
              sflush_slot_toNat sp hs 24 (by decide) (by decide)]
            omega]
        have ht : tohostAddr = 0x8001ad00 := rfl
        have := hs.htif
        omega
      · exact hc

theorem sflushM3_code (m : Mem) (sp s1 : BitVec 64)
    (hs : SflushStackOK sp) (hc : Vsa.Sim.Code.__sflush_rLoaded m) :
    Vsa.Sim.Code.__sflush_rLoaded (sflushM3 m sp s1) := by
  unfold sflushM3
  apply sflushLoaded_writeMap8
  · right; decide
  · apply sflushLoaded_writeMap8
    · right
      have hsp48 : 48 ≤ sp.toNat := by
        have ht : tohostAddr = 0x8001ad00 := rfl
        have := hs.htif
        omega
      rw [show (sflushSpE sp + sign_extend (m := 64) (0x018#12)).toNat =
        sp.toNat - 24 by
          rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
            sflush_slot_toNat sp hs 24 (by decide) (by decide)]
          omega]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hs.htif
      omega
    · exact hc

def sflushEcf4L : GRegs :=
  sflush_rXecf4L (BitVec.ofNat 64 consoleStdout) 1#64
    (BitVec.ofNat 64 consoleBuf) (BitVec.ofNat 64 consoleReent)

def sflushEcf4Lds : List (List (BitVec 8)) :=
  [[0xd4#8, 0xef#8, 0x00#8, 0x80#8, 0#8, 0#8, 0#8, 0#8],
   [0x20#8, 0xbb#8, 0x01#8, 0x80#8, 0#8, 0#8, 0#8, 0#8]]

/-- Exact live register image immediately before `jalr a5` at `0x8000ed08`.
In particular, the original `s1`/`s2` have already been spilled; their live
registers now carry the one-byte count and buffer pointer used by the callback. -/
def sflushL4 (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(10, BitVec.ofNat 64 consoleReent),
   (12, BitVec.ofNat 64 consoleBuf), (13, 1#64),
   (11, BitVec.ofNat 64 consoleStdout),
   (15, BitVec.ofNat 64 consoleSwrite),
   (9, 1#64), (14, 2#64), (18, BitVec.ofNat 64 consoleBuf),
   (19, BitVec.ofNat 64 consoleReent), (8, BitVec.ofNat 64 consoleStdout),
   (2, sflushSpE sp), (1, ra)]

theorem sflushEcf4_facts (mc m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64)
    (hc : ConsoleStream m) (hcode : Vsa.Sim.Code.__sflush_rLoaded mc) :
    ChainFacts mc m (sflushL3 sp s0 s1 s2 s3 ra) sflushEcf4Lds
      sflush_rXecf4Seg := by
  chain_facts hcode with "Vsa.Sim.Code.__sflush_r_at_"
  · unfold MemFacts
    change (0x80000000 ≤ consoleStdout + 64 ∧
      consoleStdout + 64 + 8 ≤ 0x100000000 ∧
      (consoleStdout + 64 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ consoleStdout + 64)) ∧
      LPins8 m (consoleStdout + 64)
        [0xd4#8, 0xef#8, 0x00#8, 0x80#8, 0#8, 0#8, 0#8, 0#8]
    exact ⟨⟨by decide, by decide, by right; decide⟩,
      lpins8_consoleSwrite hc.writer⟩
  · unfold MemFacts
    change (0x80000000 ≤ consoleStdout + 48 ∧
      consoleStdout + 48 + 8 ≤ 0x100000000 ∧
      (consoleStdout + 48 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ consoleStdout + 48)) ∧
      LPins8 m (consoleStdout + 48)
        [0x20#8, 0xbb#8, 0x01#8, 0x80#8, 0#8, 0#8, 0#8, 0#8]
    exact ⟨⟨by decide, by decide, by right; decide⟩,
      lpins8_consoleStdout hc.cookie⟩

theorem sflushEcf4_regs_boundary
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runChain sflush_rXecf4Seg (sflushL3 sp s0 s1 s2 s3 ra) sflushEcf4Lds =
      sflushL4 sp s0 s1 s2 s3 ra := by
  rfl

def sflushLoadsChain : List BBlock → List (List (BitVec 8)) →
    List (List (BitVec 8))
  | [], lds => lds
  | b :: bs, lds => sflushLoadsChain bs (ldsRunM b.body lds)

theorem sflushEcf4_loads_boundary :
    sflushLoadsChain sflush_rXecf4Seg sflushEcf4Lds = [] := by
  rfl

theorem sflushEcf4_mem_boundary
    (m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64) :
    memChain sflush_rXecf4Seg m (sflushL3 sp s0 s1 s2 s3 ra) sflushEcf4Lds = m := by
  rfl

theorem chainFacts_append_calc
    (mc m : Mem) (L : GRegs) (lds : List (List (BitVec 8)))
    (xs ys : List BBlock)
    (hx : ChainFacts mc m L lds xs)
    (hy : ChainFacts mc (memChain xs m L lds) (runChain xs L lds)
      (sflushLoadsChain xs lds) ys) :
    ChainFacts mc m L lds (xs ++ ys) := by
  induction xs generalizing m L lds with
  | nil => exact hy
  | cons b bs ih =>
      exact ⟨hx.1, ih _ _ _ hx.2 hy⟩

theorem runChain_append_calc
    (xs ys : List BBlock) (L : GRegs) (lds : List (List (BitVec 8))) :
    runChain (xs ++ ys) L lds =
      runChain ys (runChain xs L lds) (sflushLoadsChain xs lds) := by
  induction xs generalizing L lds with
  | nil => rfl
  | cons b bs ih => exact ih _ _

theorem memChain_append_calc
    (xs ys : List BBlock) (m : Mem) (L : GRegs)
    (lds : List (List (BitVec 8))) :
    memChain (xs ++ ys) m L lds =
      memChain ys (memChain xs m L lds) (runChain xs L lds)
        (sflushLoadsChain xs lds) := by
  induction xs generalizing m L lds with
  | nil => rfl
  | cons b bs ih => exact ih _ _ _

private def sflushL1a (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(14, 0x200a#64), (9, s1), (18, s2),
   (11, BitVec.ofNat 64 consoleStdout), (2, sp), (8, s0), (19, s3),
   (1, ra), (10, BitVec.ofNat 64 consoleReent)]

private def sflushL1b (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(2, sflushSpE sp), (14, 0x200a#64), (9, s1), (18, s2),
   (11, BitVec.ofNat 64 consoleStdout), (8, s0), (19, s3),
   (1, ra), (10, BitVec.ofNat 64 consoleReent)]

private def sflushL1c (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(15, 8#64), (2, sflushSpE sp), (14, 0x200a#64), (9, s1), (18, s2),
   (11, BitVec.ofNat 64 consoleStdout), (8, s0), (19, s3),
   (1, ra), (10, BitVec.ofNat 64 consoleReent)]

private def sflushL1d (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(8, BitVec.ofNat 64 consoleStdout), (15, 8#64), (2, sflushSpE sp),
   (14, 0x200a#64), (9, s1), (18, s2),
   (11, BitVec.ofNat 64 consoleStdout), (19, s3), (1, ra),
   (10, BitVec.ofNat 64 consoleReent)]

private theorem sflushEb70_run_lh
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runGM
      [(mkLine 0x8000eb70#64 0x01059703#32),
       (mkLine 0x8000eb74#64 0xfd010113#32),
       (mkLine 0x8000eb78#64 0x02813023#32),
       (mkLine 0x8000eb7c#64 0x01313423#32),
       (mkLine 0x8000eb80#64 0x02113423#32),
       (mkLine 0x8000eb84#64 0x00877793#32),
       (mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushConsoleL sp s0 s1 s2 s3 ra) sflushConsoleLds =
    runGM
      [(mkLine 0x8000eb74#64 0xfd010113#32),
       (mkLine 0x8000eb78#64 0x02813023#32),
       (mkLine 0x8000eb7c#64 0x01313423#32),
       (mkLine 0x8000eb80#64 0x02113423#32),
       (mkLine 0x8000eb84#64 0x00877793#32),
       (mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1a sp s0 s1 s2 s3 ra) sflushConsoleLds.tail := rfl

private theorem sflushEb70_run_addi
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runGM
      [(mkLine 0x8000eb74#64 0xfd010113#32),
       (mkLine 0x8000eb78#64 0x02813023#32),
       (mkLine 0x8000eb7c#64 0x01313423#32),
       (mkLine 0x8000eb80#64 0x02113423#32),
       (mkLine 0x8000eb84#64 0x00877793#32),
       (mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1a sp s0 s1 s2 s3 ra) sflushConsoleLds.tail =
    runGM
      [(mkLine 0x8000eb78#64 0x02813023#32),
       (mkLine 0x8000eb7c#64 0x01313423#32),
       (mkLine 0x8000eb80#64 0x02113423#32),
       (mkLine 0x8000eb84#64 0x00877793#32),
       (mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1b sp s0 s1 s2 s3 ra) sflushConsoleLds.tail := rfl

private theorem sflushEb70_run_stores
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runGM
      [(mkLine 0x8000eb78#64 0x02813023#32),
       (mkLine 0x8000eb7c#64 0x01313423#32),
       (mkLine 0x8000eb80#64 0x02113423#32),
       (mkLine 0x8000eb84#64 0x00877793#32),
       (mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1b sp s0 s1 s2 s3 ra) sflushConsoleLds.tail =
    runGM
      [(mkLine 0x8000eb84#64 0x00877793#32),
       (mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1b sp s0 s1 s2 s3 ra) sflushConsoleLds.tail := rfl

set_option maxRecDepth 1000 in
private theorem sflushEb70_step_andi
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    stepGM (mkLine 0x8000eb84#64 0x00877793#32)
      (sflushL1b sp s0 s1 s2 s3 ra) (sflushConsoleLds.tail.headD []) =
      sflushL1c sp s0 s1 s2 s3 ra := by
  change
    (15, (0x200a#64 &&& sign_extend (m := 64) (0x008#12))) ::
      eraseG 15 (sflushL1b sp s0 s1 s2 s3 ra) =
      sflushL1c sp s0 s1 s2 s3 ra
  rw [show (0x200a#64 &&& sign_extend (m := 64) (0x008#12)) = 8#64 by decide]
  rfl

private theorem sflushEb70_run_andi
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runGM
      [(mkLine 0x8000eb84#64 0x00877793#32),
       (mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1b sp s0 s1 s2 s3 ra) sflushConsoleLds.tail =
    runGM
      [(mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1c sp s0 s1 s2 s3 ra) sflushConsoleLds.tail := by
  rw [show runGM
      [(mkLine 0x8000eb84#64 0x00877793#32),
       (mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1b sp s0 s1 s2 s3 ra) sflushConsoleLds.tail =
      runGM
        [(mkLine 0x8000eb88#64 0x00058413#32),
         (mkLine 0x8000eb8c#64 0x00050993#32)]
        (stepGM (mkLine 0x8000eb84#64 0x00877793#32)
          (sflushL1b sp s0 s1 s2 s3 ra) (sflushConsoleLds.tail.headD []))
        sflushConsoleLds.tail by rfl,
    sflushEb70_step_andi]

private theorem sflushEb70_run_mv_s0
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runGM
      [(mkLine 0x8000eb88#64 0x00058413#32),
       (mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1c sp s0 s1 s2 s3 ra) sflushConsoleLds.tail =
    runGM [(mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1d sp s0 s1 s2 s3 ra) sflushConsoleLds.tail := rfl

private theorem sflushEb70_run_mv_s3
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runGM [(mkLine 0x8000eb8c#64 0x00050993#32)]
      (sflushL1d sp s0 s1 s2 s3 ra) sflushConsoleLds.tail =
      sflushL1 sp s0 s1 s2 s3 ra := rfl

theorem sflushEb70_mem_boundary
    (m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64) :
    memChain sflush_rXeb70TSeg m (sflushConsoleL sp s0 s1 s2 s3 ra)
      sflushConsoleLds = sflushM1 m sp s0 s3 ra := by
  rw [← writeLog_evalBlocks_init, sflushEntryLog_eq]
  rfl

theorem sflushEb70_regs_boundary
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runChain sflush_rXeb70TSeg (sflushConsoleL sp s0 s1 s2 s3 ra)
      sflushConsoleLds = sflushL1 sp s0 s1 s2 s3 ra := by
  change runGM
    [(mkLine 0x8000eb70#64 0x01059703#32),
     (mkLine 0x8000eb74#64 0xfd010113#32),
     (mkLine 0x8000eb78#64 0x02813023#32),
     (mkLine 0x8000eb7c#64 0x01313423#32),
     (mkLine 0x8000eb80#64 0x02113423#32),
     (mkLine 0x8000eb84#64 0x00877793#32),
     (mkLine 0x8000eb88#64 0x00058413#32),
     (mkLine 0x8000eb8c#64 0x00050993#32)]
    (sflushConsoleL sp s0 s1 s2 s3 ra) sflushConsoleLds = _
  rw [sflushEb70_run_lh, sflushEb70_run_addi, sflushEb70_run_stores,
    sflushEb70_run_andi, sflushEb70_run_mv_s0, sflushEb70_run_mv_s3]

theorem sflushEb70_loads_boundary :
    sflushLoadsChain sflush_rXeb70TSeg sflushConsoleLds =
      [flushBytes8 (BitVec.ofNat 64 consoleBuf),
       flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] := rfl

theorem sflushEcb4_mem_boundary
    (m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64) :
    memChain sflush_rXecb4FSeg m (sflushL1 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 consoleBuf),
       flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      sflushM2 m sp s2 := rfl

theorem sflushEcb4_regs_boundary
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runChain sflush_rXecb4FSeg (sflushL1 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 consoleBuf),
       flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      sflushL2 sp s0 s1 s2 s3 ra := rfl

theorem sflushEcb4_loads_boundary :
    sflushLoadsChain sflush_rXecb4FSeg
      [flushBytes8 (BitVec.ofNat 64 consoleBuf),
       flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] := rfl

theorem sflushEcc0_mem_boundary
    (m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64) :
    memChain sflush_rXecc0TSeg m (sflushL2 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      sflushM3 m sp s1 := rfl

private def sflushL2a (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(9, BitVec.ofNat 64 (consoleBuf + 1)), (18, BitVec.ofNat 64 consoleBuf),
   (19, BitVec.ofNat 64 consoleReent), (8, BitVec.ofNat 64 consoleStdout),
   (15, 8#64), (2, sflushSpE sp), (14, 0x200a#64),
   (11, BitVec.ofNat 64 consoleStdout), (1, ra),
   (10, BitVec.ofNat 64 consoleReent)]

private def sflushL2b (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(14, 2#64), (9, BitVec.ofNat 64 (consoleBuf + 1)),
   (18, BitVec.ofNat 64 consoleBuf), (19, BitVec.ofNat 64 consoleReent),
   (8, BitVec.ofNat 64 consoleStdout), (15, 8#64), (2, sflushSpE sp),
   (11, BitVec.ofNat 64 consoleStdout), (1, ra),
   (10, BitVec.ofNat 64 consoleReent)]

private def sflushL2c (sp s0 s1 s2 s3 ra : BitVec 64) : GRegs :=
  [(9, 1#64), (14, 2#64), (18, BitVec.ofNat 64 consoleBuf),
   (19, BitVec.ofNat 64 consoleReent), (8, BitVec.ofNat 64 consoleStdout),
   (15, 8#64), (2, sflushSpE sp), (11, BitVec.ofNat 64 consoleStdout),
   (1, ra), (10, BitVec.ofNat 64 consoleReent)]

private theorem sflushEcc0_step_load
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    stepGM (mkLine 0x8000ecc4#64 0x0005b483#32)
      (sflushL2 sp s0 s1 s2 s3 ra)
      (flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1))) =
      sflushL2a sp s0 s1 s2 s3 ra := by
  change
    (9, bytesVal MKind.ld (flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)))) ::
      eraseG 9 (sflushL2 sp s0 s1 s2 s3 ra) = _
  rw [flushBytes8_val]
  rfl

private theorem sflushEcc0_step_andi
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    stepGM (mkLine 0x8000ecc8#64 0x00377713#32)
      (sflushL2a sp s0 s1 s2 s3 ra) [] =
      sflushL2b sp s0 s1 s2 s3 ra := by
  change
    (14, (0x200a#64 &&& sign_extend (m := 64) (0x003#12))) ::
      eraseG 14 (sflushL2a sp s0 s1 s2 s3 ra) = _
  rw [show (0x200a#64 &&& sign_extend (m := 64) (0x003#12)) = 2#64 by decide]
  rfl

private theorem sflushEcc0_step_subw
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    stepGM (mkLine 0x8000ecd0#64 0x412484bb#32)
      (sflushL2b sp s0 s1 s2 s3 ra) [] =
      sflushL2c sp s0 s1 s2 s3 ra := by
  change
    (9, sign_extend (m := 64)
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 (consoleBuf + 1)) 31 0 -
       Sail.BitVec.extractLsb (BitVec.ofNat 64 consoleBuf) 31 0)) ::
      eraseG 9 (sflushL2b sp s0 s1 s2 s3 ra) = _
  rw [show sign_extend (m := 64)
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 (consoleBuf + 1)) 31 0 -
       Sail.BitVec.extractLsb (BitVec.ofNat 64 consoleBuf) 31 0) = 1#64 by decide]
  rfl

private theorem sflushEcc0_step_li
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    stepGM (mkLine 0x8000ecd4#64 0x00000793#32)
      (sflushL2c sp s0 s1 s2 s3 ra) [] =
      sflushL3 sp s0 s1 s2 s3 ra := rfl

theorem sflushEcc0_regs_boundary
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runChain sflush_rXecc0TSeg (sflushL2 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      sflushL3 sp s0 s1 s2 s3 ra := by
  change runGM
    [(mkLine 0x8000ecc0#64 0x00913c23#32),
     (mkLine 0x8000ecc4#64 0x0005b483#32),
     (mkLine 0x8000ecc8#64 0x00377713#32),
     (mkLine 0x8000eccc#64 0x0125b023#32),
     (mkLine 0x8000ecd0#64 0x412484bb#32),
     (mkLine 0x8000ecd4#64 0x00000793#32)]
    (sflushL2 sp s0 s1 s2 s3 ra)
    [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
     flushBytes8 (BitVec.ofNat 64 consoleSwrite),
     flushBytes8 (BitVec.ofNat 64 consoleStdout)] = _
  rw [show runGM
      [(mkLine 0x8000ecc0#64 0x00913c23#32),
       (mkLine 0x8000ecc4#64 0x0005b483#32),
       (mkLine 0x8000ecc8#64 0x00377713#32),
       (mkLine 0x8000eccc#64 0x0125b023#32),
       (mkLine 0x8000ecd0#64 0x412484bb#32),
       (mkLine 0x8000ecd4#64 0x00000793#32)]
      (sflushL2 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      runGM
        [(mkLine 0x8000ecc4#64 0x0005b483#32),
         (mkLine 0x8000ecc8#64 0x00377713#32),
         (mkLine 0x8000eccc#64 0x0125b023#32),
         (mkLine 0x8000ecd0#64 0x412484bb#32),
         (mkLine 0x8000ecd4#64 0x00000793#32)]
        (sflushL2 sp s0 s1 s2 s3 ra)
        [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
         flushBytes8 (BitVec.ofNat 64 consoleSwrite),
         flushBytes8 (BitVec.ofNat 64 consoleStdout)] by rfl]
  rw [show runGM
      [(mkLine 0x8000ecc4#64 0x0005b483#32),
       (mkLine 0x8000ecc8#64 0x00377713#32),
       (mkLine 0x8000eccc#64 0x0125b023#32),
       (mkLine 0x8000ecd0#64 0x412484bb#32),
       (mkLine 0x8000ecd4#64 0x00000793#32)]
      (sflushL2 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      runGM
        [(mkLine 0x8000ecc8#64 0x00377713#32),
         (mkLine 0x8000eccc#64 0x0125b023#32),
         (mkLine 0x8000ecd0#64 0x412484bb#32),
         (mkLine 0x8000ecd4#64 0x00000793#32)]
        (sflushL2a sp s0 s1 s2 s3 ra)
        [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
         flushBytes8 (BitVec.ofNat 64 consoleStdout)] by
        rw [show runGM
          [(mkLine 0x8000ecc4#64 0x0005b483#32),
           (mkLine 0x8000ecc8#64 0x00377713#32),
           (mkLine 0x8000eccc#64 0x0125b023#32),
           (mkLine 0x8000ecd0#64 0x412484bb#32),
           (mkLine 0x8000ecd4#64 0x00000793#32)] _ _ =
          runGM
            [(mkLine 0x8000ecc8#64 0x00377713#32),
             (mkLine 0x8000eccc#64 0x0125b023#32),
             (mkLine 0x8000ecd0#64 0x412484bb#32),
             (mkLine 0x8000ecd4#64 0x00000793#32)]
            (stepGM (mkLine 0x8000ecc4#64 0x0005b483#32)
              (sflushL2 sp s0 s1 s2 s3 ra)
              (flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1))))
            [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
             flushBytes8 (BitVec.ofNat 64 consoleStdout)] by rfl]
        rw [sflushEcc0_step_load]]
  rw [show runGM
      [(mkLine 0x8000ecc8#64 0x00377713#32),
       (mkLine 0x8000eccc#64 0x0125b023#32),
       (mkLine 0x8000ecd0#64 0x412484bb#32),
       (mkLine 0x8000ecd4#64 0x00000793#32)]
      (sflushL2a sp s0 s1 s2 s3 ra) _ =
      runGM
        [(mkLine 0x8000eccc#64 0x0125b023#32),
         (mkLine 0x8000ecd0#64 0x412484bb#32),
         (mkLine 0x8000ecd4#64 0x00000793#32)]
        (sflushL2b sp s0 s1 s2 s3 ra) _ by
        rw [show runGM _ _ _ = runGM _
          (stepGM (mkLine 0x8000ecc8#64 0x00377713#32)
            (sflushL2a sp s0 s1 s2 s3 ra) []) _ by rfl]
        rw [sflushEcc0_step_andi]]
  rw [show runGM
      [(mkLine 0x8000eccc#64 0x0125b023#32),
       (mkLine 0x8000ecd0#64 0x412484bb#32),
       (mkLine 0x8000ecd4#64 0x00000793#32)]
      (sflushL2b sp s0 s1 s2 s3 ra) _ =
      runGM
        [(mkLine 0x8000ecd0#64 0x412484bb#32),
         (mkLine 0x8000ecd4#64 0x00000793#32)]
        (sflushL2b sp s0 s1 s2 s3 ra) _ by rfl]
  rw [show runGM
      [(mkLine 0x8000ecd0#64 0x412484bb#32),
       (mkLine 0x8000ecd4#64 0x00000793#32)]
      (sflushL2b sp s0 s1 s2 s3 ra) _ =
      runGM [(mkLine 0x8000ecd4#64 0x00000793#32)]
        (sflushL2c sp s0 s1 s2 s3 ra) _ by
        rw [show runGM _ _ _ = runGM _
          (stepGM (mkLine 0x8000ecd0#64 0x412484bb#32)
            (sflushL2b sp s0 s1 s2 s3 ra) []) _ by rfl]
        rw [sflushEcc0_step_subw]]
  rw [show runGM [(mkLine 0x8000ecd4#64 0x00000793#32)]
      (sflushL2c sp s0 s1 s2 s3 ra) _ =
      sflushL3 sp s0 s1 s2 s3 ra by
        rw [show runGM _ _ _ = runGM []
          (stepGM (mkLine 0x8000ecd4#64 0x00000793#32)
            (sflushL2c sp s0 s1 s2 s3 ra) []) [] by rfl]
        exact sflushEcc0_step_li sp s0 s1 s2 s3 ra]

theorem sflushEcc0_loads_boundary :
    sflushLoadsChain sflush_rXecc0TSeg
      [flushBytes8 (BitVec.ofNat 64 (consoleBuf + 1)),
       flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] := rfl

private theorem sflushEce0_store_head
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    wentryM (mkLine 0x8000ece0#64 0x00f42623#32)
      (sflushL3 sp s0 s1 s2 s3 ra) =
      (consoleStdout + 12, 4, 0#64) := by
  unfold wentryM
  change
    (((BitVec.ofNat 64 consoleStdout : BitVec 64) +
      sign_extend (m := 64) (0x00c#12)).toNat, 4, 0#64) = _
  decide

private theorem sflushEce0_store_wlog
    (sp s0 s1 s2 s3 ra : BitVec 64)
    (lds : List (List (BitVec 8))) :
    wlogM [(mkLine 0x8000ece0#64 0x00f42623#32)]
      (sflushL3 sp s0 s1 s2 s3 ra) lds =
      [wentryM (mkLine 0x8000ece0#64 0x00f42623#32)
        (sflushL3 sp s0 s1 s2 s3 ra)] := rfl

private theorem sflushEce0_log_boundary
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    (evalBlocks sflush_rXece0TSeg
      (SegEvalState.init (sflushL3 sp s0 s1 s2 s3 ra)
        [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
         flushBytes8 (BitVec.ofNat 64 consoleStdout)])).log =
      [(consoleStdout + 12, 4, 0#64)] := by
  change [] ++ wlogM [(mkLine 0x8000ece0#64 0x00f42623#32)]
    (sflushL3 sp s0 s1 s2 s3 ra)
    [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
     flushBytes8 (BitVec.ofNat 64 consoleStdout)] = _
  rw [sflushEce0_store_wlog, sflushEce0_store_head]
  rfl

theorem sflushEce0_mem_boundary
    (m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64) :
    memChain sflush_rXece0TSeg m (sflushL3 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      writeMap4 m (consoleStdout + 12) (swData (0#64)) := by
  rw [← writeLog_evalBlocks_init, sflushEce0_log_boundary]
  rfl

theorem sflushEce0_regs_boundary
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runChain sflush_rXece0TSeg (sflushL3 sp s0 s1 s2 s3 ra)
      [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      sflushL3 sp s0 s1 s2 s3 ra := rfl

theorem sflushEce0_loads_boundary :
    sflushLoadsChain sflush_rXece0TSeg
      [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] =
      [flushBytes8 (BitVec.ofNat 64 consoleSwrite),
       flushBytes8 (BitVec.ofNat 64 consoleStdout)] := rfl

theorem sflushConsolePrefix_facts_all
    (m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64) (ch : BitVec 8)
    (hs : SflushStackOK sp) (hc : ConsoleFlushState m ch)
    (hcode : Vsa.Sim.Code.__sflush_rLoaded m) :
    ChainFacts m m
      (sflushConsoleL sp s0 s1 s2 s3 ra) sflushConsoleLds
      sflushConsolePrefixSeg := by
  let m1 := sflushM1 m sp s0 s3 ra
  let m2 := sflushM2 m1 sp s2
  let m3 := sflushM3 m2 sp s1
  let m4 := sflushM4 m2 sp s1
  have hc1 : ConsoleFlushState m1 ch := sflushM1_console m sp s0 s3 ra hs hc
  have hcode1 : Vsa.Sim.Code.__sflush_rLoaded m1 :=
    sflushM1_code m sp s0 s3 ra hs hcode
  have hc2 : ConsoleFlushState m2 ch := sflushM2_console m1 sp s2 hs hc1
  have hcode2 : Vsa.Sim.Code.__sflush_rLoaded m2 :=
    sflushM2_code m1 sp s2 hs hcode1
  have hcode3 : Vsa.Sim.Code.__sflush_rLoaded m3 :=
    sflushM3_code m2 sp s1 hs hcode2
  have hc4 : ConsoleStream m4 := sflushM4_console m2 sp s1 hs hc2
  have hcode4 : Vsa.Sim.Code.__sflush_rLoaded m4 :=
    sflushM4_code m2 sp s1 hs hcode2
  have h1 := sflushConsolePrefix_facts m m sp s0 s1 s2 s3 ra hc hs hcode
  have h2 := sflushEcb4_facts m m1 sp s0 s1 s2 s3 ra hs hc1 hcode
  have h3 := sflushEcc0_facts m m2 sp s0 s1 s2 s3 ra hs hc2 hcode
  have h4 := sflushEce0_facts m m3 sp s0 s1 s2 s3 ra hcode
  have h5 := sflushEcf4_facts m m4 sp s0 s1 s2 s3 ra hc4 hcode
  rw [sflushConsolePrefixSeg, List.append_assoc, List.append_assoc,
    List.append_assoc]
  apply chainFacts_append_calc _ _ _ _ _ _ h1
  rw [sflushEb70_mem_boundary, sflushEb70_regs_boundary,
    sflushEb70_loads_boundary]
  apply chainFacts_append_calc _ _ _ _ _ _ h2
  rw [sflushEcb4_mem_boundary, sflushEcb4_regs_boundary,
    sflushEcb4_loads_boundary]
  apply chainFacts_append_calc _ _ _ _ _ _ h3
  rw [sflushEcc0_mem_boundary, sflushEcc0_regs_boundary,
    sflushEcc0_loads_boundary]
  apply chainFacts_append_calc _ _ _ _ _ _ h4
  rw [sflushEce0_mem_boundary, sflushEce0_regs_boundary,
    sflushEce0_loads_boundary]
  simpa [m1, m2, m3, m4, sflushM4] using h5

theorem sflushConsolePrefix_regs
    (sp s0 s1 s2 s3 ra : BitVec 64) :
    runChain sflushConsolePrefixSeg (sflushConsoleL sp s0 s1 s2 s3 ra)
      sflushConsoleLds = sflushL4 sp s0 s1 s2 s3 ra := by
  rw [sflushConsolePrefixSeg, List.append_assoc, List.append_assoc,
    List.append_assoc]
  rw [runChain_append_calc, sflushEb70_regs_boundary,
    sflushEb70_loads_boundary]
  rw [runChain_append_calc, sflushEcb4_regs_boundary,
    sflushEcb4_loads_boundary]
  rw [runChain_append_calc, sflushEcc0_regs_boundary,
    sflushEcc0_loads_boundary]
  rw [runChain_append_calc, sflushEce0_regs_boundary,
    sflushEce0_loads_boundary]
  exact sflushEcf4_regs_boundary sp s0 s1 s2 s3 ra

theorem sflushConsolePrefix_mem
    (m : Mem) (sp s0 s1 s2 s3 ra : BitVec 64) :
    memChain sflushConsolePrefixSeg m (sflushConsoleL sp s0 s1 s2 s3 ra)
      sflushConsoleLds =
      sflushM4 (sflushM2 (sflushM1 m sp s0 s3 ra) sp s2) sp s1 := by
  rw [sflushConsolePrefixSeg, List.append_assoc, List.append_assoc,
    List.append_assoc]
  rw [memChain_append_calc, sflushEb70_mem_boundary,
    sflushEb70_regs_boundary, sflushEb70_loads_boundary]
  rw [memChain_append_calc, sflushEcb4_mem_boundary,
    sflushEcb4_regs_boundary, sflushEcb4_loads_boundary]
  rw [memChain_append_calc, sflushEcc0_mem_boundary,
    sflushEcc0_regs_boundary, sflushEcc0_loads_boundary]
  rw [memChain_append_calc, sflushEce0_mem_boundary,
    sflushEce0_regs_boundary, sflushEce0_loads_boundary]
  exact sflushEcf4_mem_boundary _ sp s0 s1 s2 s3 ra

def sflushClosedM (g : SflushG) : Mem :=
  sflushM4 (sflushM2 (sflushM1 g.m0 g.sp g.s0 g.sv.s3 g.ra)
    g.sp g.sv.s2) g.sp g.sv.s1

theorem sflushClosedM_console (g : SflushG) (hg : SflushGOk g) :
    ConsoleStream (sflushClosedM g) := by
  have hc1 := sflushM1_console g.m0 g.sp g.s0 g.sv.s3 g.ra
    hg.stack hg.console
  have hc2 := sflushM2_console (sflushM1 g.m0 g.sp g.s0 g.sv.s3 g.ra)
    g.sp g.sv.s2 hg.stack hc1
  exact sflushM4_console
    (sflushM2 (sflushM1 g.m0 g.sp g.s0 g.sv.s3 g.ra) g.sp g.sv.s2)
    g.sp g.sv.s1 hg.stack hc2

theorem sflushClosedM_buffer (g : SflushG) (hg : SflushGOk g) :
    (sflushClosedM g)[consoleBuf]? = some g.ch := by
  have hc1 := sflushM1_console g.m0 g.sp g.s0 g.sv.s3 g.ra
    hg.stack hg.console
  have hc2 := sflushM2_console (sflushM1 g.m0 g.sp g.s0 g.sv.s3 g.ra)
    g.sp g.sv.s2 hg.stack hc1
  have hc3 := sflushStack24_console
    (sflushM2 (sflushM1 g.m0 g.sp g.s0 g.sv.s3 g.ra) g.sp g.sv.s2)
    g.sp g.sv.s1 hg.stack hc2
  unfold sflushClosedM sflushM4 sflushM3
  rw [getElem_writeMap4_disjoint _ _ _ _ (by right; decide),
    getElem_writeMap8_disjoint _ _ _ _ (by right; decide)]
  exact hc3.bufferByte

theorem sflushClosedM_agree_lo (g : SflushG) (hg : SflushGOk g) :
    ∀ j, j < tohostAddr → (sflushClosedM g)[j]? = g.m0[j]? := by
  intro j hj
  have h8 : (sflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat =
      g.sp.toNat - 40 := by
    rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
      sflush_slot_toNat g.sp hg.stack 8 (by decide) (by decide)]
    have := hg.stack.htif
    omega
  have h16 : (sflushSpE g.sp + sign_extend (m := 64) (0x010#12)).toNat =
      g.sp.toNat - 32 := by
    rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      sflush_slot_toNat g.sp hg.stack 16 (by decide) (by decide)]
    have := hg.stack.htif
    omega
  have h24 : (sflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
      g.sp.toNat - 24 := by
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide)]
    have := hg.stack.htif
    omega
  have h32 : (sflushSpE g.sp + sign_extend (m := 64) (0x020#12)).toNat =
      g.sp.toNat - 16 := by
    rw [show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
      sflush_slot_toNat g.sp hg.stack 32 (by decide) (by decide)]
    have := hg.stack.htif
    omega
  have h40 : (sflushSpE g.sp + sign_extend (m := 64) (0x028#12)).toNat =
      g.sp.toNat - 8 := by
    rw [show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
      sflush_slot_toNat g.sp hg.stack 40 (by decide) (by decide)]
    have := hg.stack.htif
    omega
  have hsep := hg.stack.htif
  have hsp48 : 48 ≤ g.sp.toNat := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    omega
  have hjframe : j < g.sp.toNat - 48 := by omega
  have hj8 : j < (sflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat := by
    rw [h8]
    exact Nat.lt_of_lt_of_le hjframe (Nat.sub_le_sub_left (by decide) g.sp.toNat)
  have hj16 : j < (sflushSpE g.sp + sign_extend (m := 64) (0x010#12)).toNat := by
    rw [h16]
    exact Nat.lt_of_lt_of_le hjframe (Nat.sub_le_sub_left (by decide) g.sp.toNat)
  have hj24 : j < (sflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [h24]
    exact Nat.lt_of_lt_of_le hjframe (Nat.sub_le_sub_left (by decide) g.sp.toNat)
  have hj32 : j < (sflushSpE g.sp + sign_extend (m := 64) (0x020#12)).toNat := by
    rw [h32]
    exact Nat.lt_of_lt_of_le hjframe (Nat.sub_le_sub_left (by decide) g.sp.toNat)
  have hj40 : j < (sflushSpE g.sp + sign_extend (m := 64) (0x028#12)).toNat := by
    rw [h40]
    exact Nat.lt_of_lt_of_le hjframe (Nat.sub_le_sub_left (by decide) g.sp.toNat)
  have hm1 : (sflushM1 g.m0 g.sp g.s0 g.sv.s3 g.ra)[j]? = g.m0[j]? := by
    unfold sflushM1 sflushEntryLog writeLog
    simp only [List.foldl_cons, List.foldl_nil, applyW]
    rw [getElem_writeMap8_disjoint _ _ j _ (Or.inl hj40),
      getElem_writeMap8_disjoint _ _ j _ (Or.inl hj8),
      getElem_writeMap8_disjoint _ _ j _ (Or.inl hj32)]
  have hm2 :
      (sflushM2 (sflushM1 g.m0 g.sp g.s0 g.sv.s3 g.ra) g.sp g.sv.s2)[j]? =
        g.m0[j]? := by
    unfold sflushM2
    rw [getElem_writeMap8_disjoint _ _ j _ (Or.inl hj16), hm1]
  have hm3 :
      (sflushM3 (sflushM2 (sflushM1 g.m0 g.sp g.s0 g.sv.s3 g.ra)
        g.sp g.sv.s2) g.sp g.sv.s1)[j]? = g.m0[j]? := by
    unfold sflushM3
    rw [getElem_writeMap8_disjoint _ consoleStdout j _ (by
        left; have ht : tohostAddr = 0x8001ad00 := rfl
        have hc : consoleStdout = 0x8001bb20 := rfl
        omega),
      getElem_writeMap8_disjoint _ _ j _ (Or.inl hj24), hm2]
  unfold sflushClosedM sflushM4
  rw [getElem_writeMap4_disjoint _ (consoleStdout + 12) j _ (by
      left; have ht : tohostAddr = 0x8001ad00 := rfl
      have hc : consoleStdout = 0x8001bb20 := rfl
      omega), hm3]

def sflushLiveSV (g : SflushG) : SRegs :=
  { s1 := 1#64
    s2 := BitVec.ofNat 64 consoleBuf
    s3 := BitVec.ofNat 64 consoleReent
    s4 := g.sv.s4, s5 := g.sv.s5, s6 := g.sv.s6
    s7 := g.sv.s7, s8 := g.sv.s8, s9 := g.sv.s9
    s10 := g.sv.s10, s11 := g.sv.s11 }

def sflushSWG (g : SflushG) : SWG :=
  { cookie := BitVec.ofNat 64 consoleReent
    fp := BitVec.ofNat 64 consoleStdout
    buf := BitVec.ofNat 64 consoleBuf
    len := 1#64
    ra0 := 0x8000ed0c#64
    sp0 := sflushSpE g.sp
    s00 := BitVec.ofNat 64 consoleStdout
    sv := sflushLiveSV g
    fl0 := 0x0a#8, fl1 := 0x20#8
    fd0 := 1#8, fd1 := 0#8
    bytes := [g.ch]
    m0 := sflushClosedM g
    out0 := g.out0 }

theorem sflushSWG_ok (g : SflushG) (hg : SflushGOk g) :
    SWGOk (sflushSWG g) := by
  have hc := sflushClosedM_console g hg
  have hfd := readLE_two_one_bytes hc.fd
  have hsp := sflush_spE_toNat g.sp hg.stack
  have hsp96 : 96 ≤ g.sp.toNat := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hg.stack.callbackHtif
    omega
  exact
    { len_bytes := by simp [sflushSWG]
      nowrap := by simp [sflushSWG]; decide
      lo := by simp [sflushSWG]; decide
      hiram := by simp [sflushSWG]; decide
      htif := by simp [sflushSWG]; right; decide
      pins := by
        intro i hi
        change i < [g.ch].length at hi
        have hz : i = 0 := by simpa using hi
        subst i
        change (sflushClosedM g)[consoleBuf]? = some g.ch
        exact sflushClosedM_buffer g hg
      code := by
        show Vsa.Sim.Code._writeLoaded (sflushClosedM g)
        exact writeLoaded_of_agree_lo (sflushClosedM_agree_lo g hg) hg.codeW
      codeR := by
        show Vsa.Sim.Code._write_rLoaded (sflushClosedM g)
        exact write_rLoaded_of_agree_lo (sflushClosedM_agree_lo g hg) hg.codeR
      codeS := by
        show Vsa.Sim.Code.__swriteLoaded (sflushClosedM g)
        exact swriteLoaded_of_agree_lo (sflushClosedM_agree_lo g hg) hg.codeS
      ra_align := by simp [sflushSWG]
      ra_fix := by
        simp only [sflushSWG]
        apply BitVec.eq_of_toNat_eq
        decide
      sp_htif := by
        show tohostAddr + 16 ≤ (sflushSpE g.sp).toNat - 48
        rw [hsp, Nat.sub_sub]
        simpa using hg.stack.callbackHtif
      sp_errno := by
        show wrErrnoAddr + 4 ≤ (sflushSpE g.sp).toNat - 48
        rw [hsp, Nat.sub_sub]
        simpa using hg.stack.callbackErrno
      sp_hi := by
        show (sflushSpE g.sp).toNat ≤ 0x100000000
        rw [hsp]
        exact Nat.le_trans (Nat.sub_le g.sp.toNat 48) hg.stack.hi
      sp_align := by
        show (sflushSpE g.sp).toNat % 8 = 0
        rw [hsp]
        have := hg.stack.align
        omega
      buf_stack_disj := by
        left
        show consoleBuf + 1 ≤ (sflushSpE g.sp).toNat - 48
        rw [hsp, Nat.sub_sub]
        have := hg.stack.callbackConsole
        have hb : consoleBuf + 1 ≤ consoleStdout + 184 := by decide
        exact Nat.le_trans hb this
      buf_errno_disj := by simp [sflushSWG]; right; decide
      fl_pin0 := by simpa [sflushSWG] using hc.flag0
      fl_pin1 := by simpa [sflushSWG] using hc.flag1
      fd_pin0 := by simpa [sflushSWG] using hfd.1
      fd_pin1 := by simpa [sflushSWG] using hfd.2
      fp_htif := by simp [sflushSWG]; decide
      fp_hi := by simp [sflushSWG]; decide
      fp_align := by simp [sflushSWG]; decide
      fp_stack_disj := by
        left
        show consoleStdout + 20 ≤ (sflushSpE g.sp).toNat - 48
        rw [hsp, Nat.sub_sub]
        have := hg.stack.callbackConsole
        omega
      buf_fp_disj := by simp [sflushSWG]; right; decide
      append_off := by simp [sflushSWG, swFlags]; decide }

def sflushHighKeep (v : SRegs) : GRegs :=
  [(23, v.s7), (24, v.s8), (25, v.s9), (26, v.s10), (27, v.s11)]

structure SflushFnPre (g : SflushG) (c : Config) : Prop where
  ok : SflushGOk g
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

structure SflushAtJalr (g : SflushG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sflushClosedM g
  pc : c.σ.regs.get? Register.PC = some 0x8000ed08#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 consoleReent)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 consoleStdout)
  a2 : gprGet c.σ 12 = some (BitVec.ofNat 64 consoleBuf)
  a3 : gprGet c.σ 13 = some 1#64
  a5 : gprGet c.σ 15 = some (BitVec.ofNat 64 consoleSwrite)
  sp : gprGet c.σ 2 = some (sflushSpE g.sp)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some (BitVec.ofNat 64 consoleStdout)
  sregs : GHolds c.σ (sKeepL (sflushLiveSV g))
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

theorem sflushPrefixArm (g : SflushG) (hg : SflushGOk g) :
    Triple (fun c => PCAt 0x8000eb70#64 c ∧ SflushFnPre g c)
      (SflushAtJalr g) := by
  have T := segRowFramed sflushConsolePrefixSeg
    (sflushConsoleL g.sp g.s0 g.sv.s1 g.sv.s2 g.sv.s3 g.ra)
    sflushConsoleLds 0x8000eb70#64 g.m0
    ([(3, wrGpVal), (20, g.sv.s4), (21, g.sv.s5), (22, g.sv.s6)] ++
      sflushHighKeep g.sv) g.out0 (0#4)
    (by
      show ChainOK 0x8000eb70#64 [9, 18, 11, 2, 8, 19, 1, 10]
        sflushConsolePrefixSeg
      decide)
    (by
      show FrameOK [3, 20, 21, 22, 23, 24, 25, 26, 27]
        sflushConsolePrefixSeg
      decide)
  intro c hc
  obtain ⟨hpc, hp⟩ := hc
  obtain ⟨ks1, ks2, ks3, ks4, ks5, ks6, ks7, ks8, ks9, ks10, ks11, -⟩ :=
    hp.sregs
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (sflushConsoleL g.sp g.s0 g.sv.s1 g.sv.s2 g.sv.s3 g.ra)
      sflushConsoleLds sflushConsolePrefixSeg := by
    rw [hp.mem]
    exact sflushConsolePrefix_facts_all g.m0 g.sp g.s0 g.sv.s1 g.sv.s2
      g.sv.s3 g.ra g.ch hg.stack hg.console hg.codeF
  obtain ⟨c1, hsteps, h1⟩ := T c
    { seg := ⟨hp.good, hp.mem, hpc, hp.minstret,
        ⟨ks1, ks2, hp.a1, hp.sp, hp.s0, ks3, hp.ra, hp.a0, trivial⟩,
        by show KeysOK [9, 18, 11, 2, 8, 19, 1, 10]; decide,
        hfacts, hp.tick⟩
      keep := ⟨hp.gp, ks4, ks5, ks6, ks7, ks8, ks9, ks10, ks11, trivial⟩
      out := hp.out
      pw := hp.pw
      th := hp.th }
  have hregs : GHolds c1.σ
      (sflushL4 g.sp g.s0 g.sv.s1 g.sv.s2 g.sv.s3 g.ra) := by
    have hr := h1.regs
    rw [evalBlocks_regs] at hr
    change GHolds c1.σ
      (runChain sflushConsolePrefixSeg
        (sflushConsoleL g.sp g.s0 g.sv.s1 g.sv.s2 g.sv.s3 g.ra)
        sflushConsoleLds) at hr
    rw [sflushConsolePrefix_regs] at hr
    exact hr
  obtain ⟨kgp, kh4, kh5, kh6, kh7, kh8, kh9, kh10, kh11, -⟩ := h1.keep
  refine ⟨c1, hsteps, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by
        rw [h1.mem, writeLog_evalBlocks_init, sflushConsolePrefix_mem]
        rfl
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a0 := gholds_lookup (v := BitVec.ofNat 64 consoleReent) _ hregs (by rfl)
      a1 := gholds_lookup (v := BitVec.ofNat 64 consoleStdout) _ hregs (by rfl)
      a2 := gholds_lookup (v := BitVec.ofNat 64 consoleBuf) _ hregs (by rfl)
      a3 := gholds_lookup (v := 1#64) _ hregs (by rfl)
      a5 := gholds_lookup (v := BitVec.ofNat 64 consoleSwrite) _ hregs (by rfl)
      sp := gholds_lookup (v := sflushSpE g.sp) _ hregs (by rfl)
      gp := kgp
      s0 := gholds_lookup (v := BitVec.ofNat 64 consoleStdout) _ hregs (by rfl)
      sregs := ⟨gholds_lookup (v := 1#64) _ hregs (by rfl),
        gholds_lookup (v := BitVec.ofNat 64 consoleBuf) _ hregs (by rfl),
        gholds_lookup (v := BitVec.ofNat 64 consoleReent) _ hregs (by rfl),
        kh4, kh5, kh6, kh7, kh8, kh9, kh10, kh11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

theorem sflush_jalr_tgt :
    BitVec.update (0x8000efd4#64 + sign_extend (m := 64) (0x000#12)) 0 0#1 =
      0x8000efd4#64 := by
  apply BitVec.eq_of_toNat_eq
  decide

theorem sflush_sailOutput_sigmaPost_jalr
    (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).sailOutput = σ.sailOutput := rfl

theorem sflushArmJalr (g : SflushG) (hg : SflushGOk g) :
    Triple (SflushAtJalr g)
      (fun c => PCAt 0x8000efd4#64 c ∧ SwFnPre (sflushSWG g) c) := by
  intro c hA
  obtain ⟨vm1, hmi1⟩ := hA.minstret
  have hcF : Vsa.Sim.Code.__sflush_rLoaded c.σ.mem := by
    rw [hA.mem]
    apply sflushLoaded_of_agree g.m0 (sflushClosedM g)
    · intro a hlo hhi
      exact sflushClosedM_agree_lo g hg a (by
        have ht : tohostAddr = 0x8001ad00 := rfl
        omega)
    · exact hg.codeF
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__sflush_r_at_8000ed08 hcF
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jalr c.σ c.tick c.steps (0x8000ed08#64) vm1 (0x8000efd4#64)
      (0x000780e7#32) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x01#5)
      Register.x1 (BitVec.addInt (0x8000ed08#64) 4)
      (0xe7#8) (0x80#8) (0x07#8) (0x00#8)
      hA.good hA.pc hmi1 hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_000780e7 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.mseccfg))
      (rX_bits_x15 _ (0x8000efd4#64)
        (by rw [get?_afterNextPC c.σ (0x8000ed08#64) _ (by decide) (by decide)]
            exact hA.a5))
      (by rw [sflush_jalr_tgt]; decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000ed08#64) 4)) hA.tick
  rw [sflush_jalr_tgt] at hobs
  refine ⟨⟨σ2, i2, c.steps + 1⟩, Steps.head hstep (Steps.refl _), ?_, ?_⟩
  · exact obs_jalr_pc hobs
  · exact
      { ok := sflushSWG_ok g hg
        good := hG2
        tick := hi2
        mem := hmem2.trans hA.mem
        minstret := obs_jalr_minstret hobs
        a0 := obs_jalr_other hobs Register.x10 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a0
        a1 := obs_jalr_other hobs Register.x11 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a1
        a2 := obs_jalr_other hobs Register.x12 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a2
        a3 := obs_jalr_other hobs Register.x13 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a3
        ra := by
          have h := obs_jalr_rd hobs (by decide) (by decide) (by decide)
            (by decide) (by decide)
          show gprGet σ2 1 = some 0x8000ed0c#64
          rwa [show BitVec.addInt (0x8000ed08#64) 4 = (0x8000ed0c#64 : BitVec 64)
            from by apply BitVec.eq_of_toNat_eq; decide] at h
        sp := obs_jalr_other hobs Register.x2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.sp
        gp := obs_jalr_other hobs Register.x3 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.gp
        s0 := obs_jalr_other hobs Register.x8 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.s0
        sregs := by
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hA.sregs
          exact ⟨
            obs_jalr_other hobs Register.x9 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k1,
            obs_jalr_other hobs Register.x18 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k2,
            obs_jalr_other hobs Register.x19 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k3,
            obs_jalr_other hobs Register.x20 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k4,
            obs_jalr_other hobs Register.x21 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k5,
            obs_jalr_other hobs Register.x22 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k6,
            obs_jalr_other hobs Register.x23 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k7,
            obs_jalr_other hobs Register.x24 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k8,
            obs_jalr_other hobs Register.x25 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k9,
            obs_jalr_other hobs Register.x26 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k10,
            obs_jalr_other hobs Register.x27 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k11,
            trivial⟩
        out := hobs.2.trans ((sflush_sailOutput_sigmaPost_jalr c.σ
          (0x8000ed08#64) vm1 (0x8000efd4#64) Register.x1
          (BitVec.addInt (0x8000ed08#64) 4)).trans hA.out)
        pw := obs_jalr_other hobs Register.htif_payload_writes (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) hA.pw
        th := by
          obtain ⟨v, hv⟩ := hA.th
          exact ⟨v, obs_jalr_other hobs Register.htif_tohost (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) hv⟩ }

theorem sflushCallbackArm (g : SflushG) (hg : SflushGOk g) :
    Triple (SflushAtJalr g) (SwFnPost (sflushSWG g)) :=
  Triple.seq (sflushArmJalr g hg) (swrite_summary (sflushSWG g)).run

def sflushCallbackM (g : SflushG) : Mem :=
  wrM1 (swWRG (sflushSWG g))

/-- The callback's own nested frames, errno clear, FILE flag write, and HTIF
traffic do not touch the caller's outer `__sflush_r` frame. -/
theorem sflushCallbackM_outer (g : SflushG) (hg : SflushGOk g)
    (k : Nat) (hk : (sflushSpE g.sp).toNat ≤ k) :
    (sflushCallbackM g)[k]? = (sflushClosedM g)[k]? := by
  have hsw := sflushSWG_ok g hg
  have hwr := swWRG_ok (sflushSWG g) hsw
  have hsp := sflush_spE_toNat g.sp hg.stack
  have herr : wrErrnoAddr + 4 ≤ k := by
    have hcb := hg.stack.callbackErrno
    rw [hsp] at hk
    omega
  have hfp : consoleStdout + 18 ≤ k := by
    have hcb := hg.stack.callbackConsole
    rw [hsp] at hk
    omega
  calc
    (sflushCallbackM g)[k]? = (swWRG (sflushSWG g)).m0[k]? := by
      exact wrM1_getElem_lo (swWRG (sflushSWG g)) hwr k
        (by right; simpa [swWRG, sflushSWG] using hk) (Or.inr herr)
    _ = (sflushClosedM g)[k]? := by
      exact swM2_getElem_lo (sflushSWG g) hsw k
        (by right; simpa [sflushSWG] using hk)
        (by right; simpa [sflushSWG] using hfp)

private theorem pin8_after_write8 {m : Mem} {a : Nat} {v : BitVec 64}
    (a' : Nat) (d : BitVec 64) (hd : a + 8 ≤ a' ∨ a' + 8 ≤ a)
    (hp : Pin8 m a v) : Pin8 (writeMap8 m a' (sdData_val d)) a v :=
  Pin8_frame (fun k hk0 hk1 => getElem_writeMap8_disjoint _ _ _ _ (by
    rcases hd with h | h <;> omega)) hp

private theorem pin8_after_write4 {m : Mem} {a : Nat} {v : BitVec 64}
    (a' : Nat) (d : BitVec 32) (hd : a + 8 ≤ a' ∨ a' + 4 ≤ a)
    (hp : Pin8 m a v) : Pin8 (writeMap4 m a' d) a v :=
  Pin8_frame (fun k hk0 hk1 => getElem_writeMap4_disjoint _ _ _ _ (by
    rcases hd with h | h <;> omega)) hp

theorem sflushClosedM_pin_s1 (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushClosedM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.sv.s1 := by
  have ha : (sflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
      g.sp.toNat - 24 := by
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide)]
    have := hg.stack.htif
    omega
  unfold sflushClosedM sflushM4 sflushM3
  apply pin8_after_write4 (consoleStdout + 12) _
  · right; rw [ha]
    have := hg.stack.console
    omega
  apply pin8_after_write8 consoleStdout _
  · right; rw [ha]
    have := hg.stack.console
    omega
  exact Pin8_writeMap8 _ _ _

theorem sflushClosedM_pin_s2 (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushClosedM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x010#12)).toNat g.sv.s2 := by
  have ha16 : (sflushSpE g.sp + sign_extend (m := 64) (0x010#12)).toNat =
      g.sp.toNat - 32 := by
    rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      sflush_slot_toNat g.sp hg.stack 16 (by decide) (by decide)]
    have := hg.stack.htif; omega
  have ha24 : (sflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
      g.sp.toNat - 24 := by
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide)]
    have := hg.stack.htif; omega
  unfold sflushClosedM sflushM4 sflushM3 sflushM2
  apply pin8_after_write4 (consoleStdout + 12) _
  · right; rw [ha16]; have := hg.stack.console; omega
  apply pin8_after_write8 consoleStdout _
  · right; rw [ha16]; have := hg.stack.console; omega
  apply pin8_after_write8 _ _
  · left; rw [ha16, ha24]
    have := hg.stack.htif; omega
  exact Pin8_writeMap8 _ _ _

theorem sflushClosedM_pin_ra (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushClosedM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x028#12)).toNat g.ra := by
  have ha16 : (sflushSpE g.sp + sign_extend (m := 64) (0x010#12)).toNat =
      g.sp.toNat - 32 := by
    rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      sflush_slot_toNat g.sp hg.stack 16 (by decide) (by decide)]
    have := hg.stack.htif; omega
  have ha24 : (sflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat =
      g.sp.toNat - 24 := by
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide)]
    have := hg.stack.htif; omega
  have ha40 : (sflushSpE g.sp + sign_extend (m := 64) (0x028#12)).toNat =
      g.sp.toNat - 8 := by
    rw [show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
      sflush_slot_toNat g.sp hg.stack 40 (by decide) (by decide)]
    have := hg.stack.htif; omega
  unfold sflushClosedM sflushM4 sflushM3 sflushM2 sflushM1 sflushEntryLog writeLog
  simp only [List.foldl_cons, List.foldl_nil, applyW]
  apply pin8_after_write4 (consoleStdout + 12) _
  · right; rw [ha40]; have := hg.stack.console; omega
  apply pin8_after_write8 consoleStdout _
  · right; rw [ha40]; have := hg.stack.console; omega
  apply pin8_after_write8 _ _
  · right
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
      sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 40 (by decide) (by decide)]
    omega
  apply pin8_after_write8 _ _
  · right
    rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
      sflush_slot_toNat g.sp hg.stack 16 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 40 (by decide) (by decide)]
    omega
  exact Pin8_writeMap8 _ _ _

theorem sflushClosedM_pin_s3 (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushClosedM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat g.sv.s3 := by
  have ha8 : (sflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat =
      g.sp.toNat - 40 := by
    rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
      sflush_slot_toNat g.sp hg.stack 8 (by decide) (by decide)]
    have := hg.stack.htif; omega
  unfold sflushClosedM sflushM4 sflushM3 sflushM2 sflushM1 sflushEntryLog writeLog
  simp only [List.foldl_cons, List.foldl_nil, applyW]
  apply pin8_after_write4 (consoleStdout + 12) _
  · right; rw [ha8]; have := hg.stack.console; omega
  apply pin8_after_write8 consoleStdout _
  · right; rw [ha8]; have := hg.stack.console; omega
  apply pin8_after_write8 _ _
  · left
    rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
      show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat g.sp hg.stack 8 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide)]
    omega
  apply pin8_after_write8 _ _
  · left
    rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
      show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      sflush_slot_toNat g.sp hg.stack 8 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 16 (by decide) (by decide)]
    omega
  apply pin8_after_write8 _ _
  · left
    rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
      show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
      sflush_slot_toNat g.sp hg.stack 8 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 40 (by decide) (by decide)]
    omega
  exact Pin8_writeMap8 _ _ _

theorem sflushClosedM_pin_s0 (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushClosedM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x020#12)).toNat g.s0 := by
  have ha32 : (sflushSpE g.sp + sign_extend (m := 64) (0x020#12)).toNat =
      g.sp.toNat - 16 := by
    rw [show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
      sflush_slot_toNat g.sp hg.stack 32 (by decide) (by decide)]
    have := hg.stack.htif; omega
  unfold sflushClosedM sflushM4 sflushM3 sflushM2 sflushM1 sflushEntryLog writeLog
  simp only [List.foldl_cons, List.foldl_nil, applyW]
  apply pin8_after_write4 (consoleStdout + 12) _
  · right; rw [ha32]; have := hg.stack.console; omega
  apply pin8_after_write8 consoleStdout _
  · right; rw [ha32]; have := hg.stack.console; omega
  apply pin8_after_write8 _ _
  · right
    rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
      sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 32 (by decide) (by decide)]
    omega
  apply pin8_after_write8 _ _
  · right
    rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
      sflush_slot_toNat g.sp hg.stack 16 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 32 (by decide) (by decide)]
    omega
  apply pin8_after_write8 _ _
  · left
    rw [show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
      show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
      sflush_slot_toNat g.sp hg.stack 32 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 40 (by decide) (by decide)]
    omega
  apply pin8_after_write8 _ _
  · right
    rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
      show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
      sflush_slot_toNat g.sp hg.stack 8 (by decide) (by decide),
      sflush_slot_toNat g.sp hg.stack 32 (by decide) (by decide)]
    omega
  exact Pin8_writeMap8 _ _ _

/-- The nested `__swrite`/`_write_r` callback stays below its entry stack
pointer, so every saved word in the outer `__sflush_r` frame survives. -/
private theorem sflushCallback_pin_of_closed (g : SflushG) (hg : SflushGOk g)
    {a : Nat} {v : BitVec 64} (ha : (sflushSpE g.sp).toNat ≤ a)
    (hp : Pin8 (sflushClosedM g) a v) : Pin8 (sflushCallbackM g) a v :=
  Pin8_frame (fun k hk0 _hk1 =>
    sflushCallbackM_outer g hg k (Nat.le_trans ha hk0)) hp

private theorem flush_lpins8_of_pin8 {m : Mem} {a : Nat} {v : BitVec 64}
    (hp : Pin8 m a v) : LPins8 m a (flushBytes8 v) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := hp
  exact ⟨lpin_of_present p0, lpin_of_present p1, lpin_of_present p2,
    lpin_of_present p3, lpin_of_present p4, lpin_of_present p5,
    lpin_of_present p6, lpin_of_present p7⟩

theorem sflushCallback_pin_s1 (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat g.sv.s1 := by
  apply sflushCallback_pin_of_closed g hg
  · rw [show sign_extend (m := 64) (0x018#12) = (24#64) by decide,
      sflush_slot_toNat g.sp hg.stack 24 (by decide) (by decide),
      sflush_spE_toNat g.sp hg.stack]
    have := hg.stack.htif
    omega
  exact sflushClosedM_pin_s1 g hg

theorem sflushCallback_pin_s2 (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x010#12)).toNat g.sv.s2 := by
  apply sflushCallback_pin_of_closed g hg
  · rw [show sign_extend (m := 64) (0x010#12) = (16#64) by decide,
      sflush_slot_toNat g.sp hg.stack 16 (by decide) (by decide),
      sflush_spE_toNat g.sp hg.stack]
    have := hg.stack.htif
    omega
  exact sflushClosedM_pin_s2 g hg

theorem sflushCallback_pin_ra (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x028#12)).toNat g.ra := by
  apply sflushCallback_pin_of_closed g hg
  · rw [show sign_extend (m := 64) (0x028#12) = (40#64) by decide,
      sflush_slot_toNat g.sp hg.stack 40 (by decide) (by decide),
      sflush_spE_toNat g.sp hg.stack]
    have := hg.stack.htif
    omega
  exact sflushClosedM_pin_ra g hg

theorem sflushCallback_pin_s3 (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat g.sv.s3 := by
  apply sflushCallback_pin_of_closed g hg
  · rw [show sign_extend (m := 64) (0x008#12) = (8#64) by decide,
      sflush_slot_toNat g.sp hg.stack 8 (by decide) (by decide),
      sflush_spE_toNat g.sp hg.stack]
    have := hg.stack.htif
    omega
  exact sflushClosedM_pin_s3 g hg

theorem sflushCallback_pin_s0 (g : SflushG) (hg : SflushGOk g) :
    Pin8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x020#12)).toNat g.s0 := by
  apply sflushCallback_pin_of_closed g hg
  · rw [show sign_extend (m := 64) (0x020#12) = (32#64) by decide,
      sflush_slot_toNat g.sp hg.stack 32 (by decide) (by decide),
      sflush_spE_toNat g.sp hg.stack]
    have := hg.stack.htif
    omega
  exact sflushClosedM_pin_s0 g hg

theorem sflushCallback_lpins_s1 (g : SflushG) (hg : SflushGOk g) :
    LPins8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x018#12)).toNat
      (flushBytes8 g.sv.s1) :=
  flush_lpins8_of_pin8 (sflushCallback_pin_s1 g hg)

theorem sflushCallback_lpins_s2 (g : SflushG) (hg : SflushGOk g) :
    LPins8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x010#12)).toNat
      (flushBytes8 g.sv.s2) :=
  flush_lpins8_of_pin8 (sflushCallback_pin_s2 g hg)

theorem sflushCallback_lpins_ra (g : SflushG) (hg : SflushGOk g) :
    LPins8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x028#12)).toNat
      (flushBytes8 g.ra) :=
  flush_lpins8_of_pin8 (sflushCallback_pin_ra g hg)

theorem sflushCallback_lpins_s3 (g : SflushG) (hg : SflushGOk g) :
    LPins8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x008#12)).toNat
      (flushBytes8 g.sv.s3) :=
  flush_lpins8_of_pin8 (sflushCallback_pin_s3 g hg)

theorem sflushCallback_lpins_s0 (g : SflushG) (hg : SflushGOk g) :
    LPins8 (sflushCallbackM g)
      (sflushSpE g.sp + sign_extend (m := 64) (0x020#12)).toNat
      (flushBytes8 g.s0) :=
  flush_lpins8_of_pin8 (sflushCallback_pin_s0 g hg)

/-- Code is below HTIF.  Each nested callback frame and the outer prefix
agrees there with the original code image. -/
theorem sflushCallbackM_agree_lo (g : SflushG) (hg : SflushGOk g)
    (k : Nat) (hk : k < tohostAddr) :
    (sflushCallbackM g)[k]? = g.m0[k]? := by
  have hsw := sflushSWG_ok g hg
  have hwr := swWRG_ok (sflushSWG g) hsw
  calc
    (sflushCallbackM g)[k]? = (swWRG (sflushSWG g)).m0[k]? :=
      wrM1_agree_lo (swWRG (sflushSWG g)) hwr k hk
    _ = (sflushClosedM g)[k]? := swM2_agree_lo (sflushSWG g) hsw k hk
    _ = g.m0[k]? := sflushClosedM_agree_lo g hg k hk

theorem sflushCallbackM_code (g : SflushG) (hg : SflushGOk g) :
    Vsa.Sim.Code.__sflush_rLoaded (sflushCallbackM g) := by
  apply sflushLoaded_of_agree g.m0 (sflushCallbackM g)
  · intro a _ha hlo
    exact sflushCallbackM_agree_lo g hg a (by
      have ht : tohostAddr = 0x8001ad00 := rfl
      omega)
  exact hg.codeF

def sflushConsoleSuffixSeg : List BBlock :=
  sflush_rXed0cTSeg ++ sflush_rXececTSeg ++ sflush_rXed4cSeg ++
    sflush_rXed50Seg ++ sflush_rXec9cSeg

def sflushConsoleSuffixL (sp : BitVec 64) : GRegs :=
  [(9, 1#64), (10, 1#64), (18, BitVec.ofNat 64 consoleBuf),
   (2, sflushSpE sp)]

def sflushConsoleSuffixLds (g : SflushG) : List (List (BitVec 8)) :=
  [flushBytes8 g.sv.s1, flushBytes8 g.sv.s2, flushBytes8 g.ra,
   flushBytes8 g.s0, flushBytes8 g.sv.s3]

def sflushSuffixL1 (sp : BitVec 64) : GRegs :=
  [(9, 0#64), (10, 1#64), (18, BitVec.ofNat 64 consoleBuf),
   (2, sflushSpE sp)]

def sflushSuffixL2 (sp : BitVec 64) : GRegs :=
  [(18, (BitVec.ofNat 64 consoleBuf : BitVec 64) + 1#64),
   (9, 0#64), (10, 1#64),
   (2, sflushSpE sp)]

private theorem sflushEd0c_step (sp : BitVec 64) :
    stepGM (mkLine 0x8000ed0c#64 0x40a484bb#32)
      (sflushConsoleSuffixL sp) [] = sflushSuffixL1 sp := by
  change
    (9, sign_extend (m := 64)
      (Sail.BitVec.extractLsb (1#64) 31 0 -
       Sail.BitVec.extractLsb (1#64) 31 0)) ::
      eraseG 9 (sflushConsoleSuffixL sp) = sflushSuffixL1 sp
  rw [show sign_extend (m := 64)
      (Sail.BitVec.extractLsb (1#64) 31 0 -
       Sail.BitVec.extractLsb (1#64) 31 0) = 0#64 by decide]
  rfl

theorem sflushEd0c_run (sp : BitVec 64)
    (lds : List (List (BitVec 8))) :
    runChain sflush_rXed0cTSeg (sflushConsoleSuffixL sp) lds =
      sflushSuffixL1 sp := by
  change runGM [(mkLine 0x8000ed0c#64 0x40a484bb#32)]
      (sflushConsoleSuffixL sp) lds = _
  rw [show runGM _ _ _ = runGM []
    (stepGM (mkLine 0x8000ed0c#64 0x40a484bb#32)
      (sflushConsoleSuffixL sp) []) lds by rfl]
  exact sflushEd0c_step sp

end Vsa.Sim

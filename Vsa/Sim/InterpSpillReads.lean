import Vsa.Sim.rows.DriveSpillGen
import Vsa.Sim.WriteLogNF
import Vsa.Sim.ReprSurvival

open Vsa.MemRepr LeanRV64DExecutable LeanRV64DExecutable.Functions

namespace Vsa.Sim

def interpSpillLog (inp ra s0 s1 s2 s3 s4 s5 s6 stmts count repl : BitVec 64) : List WEntry :=
  [(0x87fffc50, 8, inp), (0x87fffcf8, 8, ra),
   (0x87fffcf0, 8, s0), (0x87fffce8, 8, s1), (0x87fffce0, 8, s2),
   (0x87fffcd8, 8, s3), (0x87fffcd0, 8, s4), (0x87fffcc8, 8, s5),
   (0x87fffcc0, 8, s6), (0x87fffc68, 8, stmts),
   (0x87fffc60, 8, count), (0x87fffc58, 8, repl)]

theorem driveSpill_log (inp ra s0 s1 s2 s3 s4 s5 s6 stmts count repl : BitVec 64) :
    (evalBlocks driveSpillSeg (SegEvalState.init
      (driveSpillL inp 0x87fffd00#64 ra s0 s1 s2 s3 s4 s5 s6 stmts count repl) [])).log =
    interpSpillLog inp ra s0 s1 s2 s3 s4 s5 s6 stmts count repl := by
  let L0 := driveSpillL inp 0x87fffd00#64 ra s0 s1 s2 s3 s4 s5 s6 stmts count repl
  let L1 : GRegs := [(2, 0x87fffc50#64), (10, inp), (1, ra), (8, s0), (9, s1),
    (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (11, stmts), (12, count), (13, repl)]
  let L2 : GRegs := [(10, inp + 16#64), (2, 0x87fffc50#64), (1, ra), (8, s0), (9, s1),
    (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (11, stmts), (12, count), (13, repl)]
  have hsp : stepGM (mkLine 0x800043ec#64 0xf5010113#32) L0 [] = L1 := by
    change (2, (0x87fffd00#64 + sign_extend (m := 64) 0xf50#12)) :: _ = L1
    rw [show (0x87fffd00#64 + sign_extend (m := 64) 0xf50#12 : BitVec 64) =
      0x87fffc50#64 by decide]
    rfl
  have ha0 : stepGM (mkLine 0x800043f4#64 0x01050513#32) L1 [] = L2 := by rfl
  change (evalBlocks driveSpillSeg (SegEvalState.init L0 [])).log = _
  simp only [driveSpillSeg, evalBlocks, evalBlock, SegEvalState.init, List.nil_append]
  rw [wlogM]
  change wlogM _ (stepGM (mkLine 0x800043ec#64 0xf5010113#32) L0 []) [] = _
  rw [hsp, wlogM]
  change wentryM (mkLine 0x800043f0#64 0x00a13023#32) L1 ::
    wlogM _ (stepGM (mkLine 0x800043f4#64 0x01050513#32) L1 []) [] = _
  rw [ha0]
  congr 1

/-- Read back one complete word written before a disjoint log suffix. -/
theorem read64_of_writeLog (m : Mem) (before after : List WEntry)
    (a : Nat) (v : BitVec 64) (hd : OutLRange after a 8) :
    read64 (writeLog m (before ++ (a, 8, v) :: after)) a = some v.toNat := by
  rw [writeLog_append]
  let written := writeMap8 (writeLog m before) a (sdData_val v)
  change read64 (writeLog written after) a = some v.toNat
  have he : read64 (writeLog written after) a = read64 written a :=
    read64_agreeP (P := OutL after) (writeLog_out written after)
      (fun k hk => outL_of_range hd (by omega) (by omega))
  rw [he, show read64 written a = some (sdData_val v).toNat from read64_writeMap8 _ _ _,
    sdData_toNat]

/-- Indexed word readback avoids repeating a concrete log's prefix and suffix. -/
theorem read64_of_writeLog_at (m : Mem) (log : List WEntry) (index a : Nat)
    (v : BitVec 64) (hi : log[index]? = some (a, 8, v))
    (hd : OutLRange (log.drop (index + 1)) a 8) :
    read64 (writeLog m log) a = some v.toNat := by
  induction log generalizing index m with
  | nil => simp at hi
  | cons entry rest ih =>
    cases index with
    | zero =>
      have he : entry = (a, 8, v) := Option.some.inj hi
      subst entry
      exact read64_of_writeLog m [] rest a v hd
    | succ i =>
      exact ih (applyW m entry) i (by simpa using hi) (by simpa using hd)

/-- The four argument words written by the concrete interpreter prologue. -/
structure InterpSpillReads (m : Mem) (inp stmts count repl : BitVec 64) : Prop where
  input : read64 m 0x87fffc50 = some inp.toNat
  statements : read64 m 0x87fffc68 = some stmts.toNat
  length : read64 m 0x87fffc60 = some count.toNat
  script : read64 m 0x87fffc58 = some repl.toNat

/-- All argument words are read back from the reflected write log. -/
theorem interpSpillLog_reads (m : Mem)
    (inp ra s0 s1 s2 s3 s4 s5 s6 stmts count repl : BitVec 64) :
    InterpSpillReads (writeLog m (interpSpillLog inp ra s0 s1 s2 s3 s4 s5 s6 stmts count repl))
      inp stmts count repl := by
  let log := interpSpillLog inp ra s0 s1 s2 s3 s4 s5 s6 stmts count repl
  constructor
  · exact read64_of_writeLog_at m log 0 _ _ rfl (by simp [log, interpSpillLog, OutLRange])
  · exact read64_of_writeLog_at m log 9 _ _ rfl (by simp [log, interpSpillLog, OutLRange])
  · exact read64_of_writeLog_at m log 10 _ _ rfl (by simp [log, interpSpillLog, OutLRange])
  · exact read64_of_writeLog_at m log 11 _ _ rfl (by simp [log, interpSpillLog, OutLRange])

/-- Agreement on the argument spill window preserves all four saved words. -/
theorem InterpSpillReads.transport {m m' : Mem} {inp stmts count repl : BitVec 64}
    (h : InterpSpillReads m inp stmts count repl)
    (ha : AgreeP (fun k => 0x87fffc50 ≤ k ∧ k < 0x87fffc70) m m') :
    InterpSpillReads m' inp stmts count repl := by
  have rd : ∀ a, 0x87fffc50 ≤ a → a + 8 ≤ 0x87fffc70 →
      read64 m a = read64 m' a :=
    fun a hlo hhi => read64_agreeP ha (fun k hk => by constructor <;> omega)
  exact ⟨(rd _ (by decide) (by decide)).symm.trans h.input,
    (rd _ (by decide) (by decide)).symm.trans h.statements,
    (rd _ (by decide) (by decide)).symm.trans h.length,
    (rd _ (by decide) (by decide)).symm.trans h.script⟩

#print axioms driveSpill_log
#print axioms read64_of_writeLog
#print axioms read64_of_writeLog_at
#print axioms interpSpillLog_reads
#print axioms InterpSpillReads.transport
end Vsa.Sim

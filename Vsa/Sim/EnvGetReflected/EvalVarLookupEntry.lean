import Vsa.Sim.EnvGetReflected.EvalVarCallFrame
import Vsa.Sim.EnvGetReflected.EnvGetLookupReturn

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The bounded spill window excludes bitvector subtraction wraparound. -/
theorem CallerTailWindow.stack_base
    {A : Arena} {SL : StackLayout} {out sp : BitVec 64}
    (w : CallerTailWindow A SL out (sp - 64#64)) :
    (sp - 64#64).toNat + 64 = sp.toNat := by
  have hbound := w.spill
  have hram := w.ram
  have h := congrArg BitVec.toNat (BitVec.sub_add_cancel sp 64#64)
  rw [BitVec.toNat_add] at h
  change ((sp - 64#64).toNat + 64) % 2^64 = sp.toNat at h
  rwa [Nat.mod_eq_of_lt (by omega)] at h

/-- The same caller window supplies lookup spill and mask separation. -/
theorem CallerTailWindow.lookup_spill
    {A : Arena} {SL : StackLayout} {out sp : BitVec 64}
    (w : CallerTailWindow A SL out (sp - 64#64)) : LookupSpillWindow A SL sp := by
  refine ⟨w.spill, w.arena, ?_⟩
  have hs := w.spill
  have ht := w.htif
  have hm : maskAddr + 8 ≤ tohostAddr + 16 := by decide
  omega

def varSavedInput (r8 r9 r18 r19 r20 r21 : BitVec 64) : GRegs :=
  [(8, r8), (9, r9), (18, r18), (19, r19), (20, r20), (21, r21)]

/-- Supply the legacy prologue carrier from the actual call and owned frame.
Only its stronger HTIF gap remains separate from the shared caller window. -/
theorem LookupData.var_prologue
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {expr name sp r8 r9 r18 r19 r20 r21 : BitVec 64}
    {fa : Nat} {bs : List (BitVec 8)} {before entry : Config}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name entry.σ.mem)
    (hfa : fa < s.frames.size)
    (hc : VarCallResult expr (BitVec.ofNat 64 (phiF fa)) sp name bs before entry)
    (hsaved : GHolds before.σ (varSavedInput r8 r9 r18 r19 r20 r21))
    (hcode : Code.Env_getLoaded entry.σ.mem)
    (w : CallerTailWindow A SL (sp + 240#64) (sp - 64#64))
    (hgap : tohostAddr + 64 ≤ sp.toNat - 64) :
    ∃ len pn, PrologueHeadSt (BitVec.ofNat 64 (phiF fa)) name (sp + 240#64)
      sp 0x80003444#64 r8 r9 r18 r19 r20 r21 len pn entry.σ.mem entry := by
  have hptr := D.framePointer hfa
  have hb := (D.repr.frames_arena fa hfa).1
  change A.lo ≤ phiF fa ∧ phiF fa + 32 ≤ A.hi at hb
  have hlo := D.arenaLo
  have hhi := D.arenaHi
  have hbase := w.stack_base
  have hspill := w.spill
  have hram := w.ram
  have hsp64 : 64 ≤ sp.toNat := by omega
  have hspHi : sp.toNat ≤ 0x100000000 := by omega
  have hspEq := sp_sub64_toNat sp hsp64
  have hout : (sp + 240#64).toNat = sp.toNat + 240 := by
    rw [BitVec.toNat_add]
    change (sp.toNat + 240) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have halign := w.outputAlign
  rw [hout] at halign
  obtain ⟨a, ha⟩ := (D.owned.frames fa hfa).arrays
  have hcount := frame_count_read (D.repr.frames fa hfa)
  obtain ⟨henv, hname, houtreg, hsp, _⟩ := hc.args
  obtain ⟨h8, h9, h18, h19, h20, h21, _⟩ := hsaved
  have hkeep (R : Register) (hr : varCallerKeep R = true) :
      entry.σ.regs.get? R = before.σ.regs.get? R := hc.caller R hr
  refine ⟨s.frames[fa].vars.length, a.names,
    { good := hc.good, loadedG := hcode, mem := rfl, pc := hc.pc
      a0 := by simpa [gprGet] using henv
      a1 := by simpa [gprGet] using hname
      a2 := by simpa [gprGet] using houtreg
      ra := hc.ra
      sp := by simpa [gprGet] using hsp
      cs8 := (hkeep .x8 (by decide)).trans (by simpa [gprGet] using h8)
      cs9 := (hkeep .x9 (by decide)).trans (by simpa [gprGet] using h9)
      cs18 := (hkeep .x18 (by decide)).trans (by simpa [gprGet] using h18)
      cs19 := (hkeep .x19 (by decide)).trans (by simpa [gprGet] using h19)
      cs20 := (hkeep .x20 (by decide)).trans (by simpa [gprGet] using h20)
      cs21 := (hkeep .x21 (by decide)).trans (by simpa [gprGet] using h21)
      minstret := hc.minstret, tick := hc.tick
      envNe := ?_
      read_len := by rw [hptr]; exact hcount
      read_pn := by rw [hptr]; exact ha.namesRead
      spDrop := hsp64
      spLo := by omega
      spHi := hspHi
      spWin := hgap
      spAlign := by omega
      spCode := ?_
      envHi := by rw [hptr]; omega
      envStackDisj := by rw [hptr]; have := w.arena; omega }⟩
  · apply Bool.eq_false_iff.mpr
    intro heq
    have hz := congrArg BitVec.toNat (beq_iff_eq.mp heq)
    rw [hptr] at hz
    change phiF fa = 0 at hz
    omega
  · right
    have ht : tohostAddr = 0x8001ad00 := rfl
    omega

/-- Run the actual variable prefix and successful lookup as one framed execution. -/
theorem var_lookup
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {v : Vsa.While.Value} {fa : Nat}
    (expr name sp r8 r9 r18 r19 r20 r21 : BitVec 64) (c : Config)
    (D : LookupData N A SL phiF phiC alloc exts shared s query name c.σ.mem)
    (hget : s.get? fa query = some v)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80003434#64)
    (htick : c.tick < 2)
    (hL : GHolds c.σ (varCallInput expr (BitVec.ofNat 64 (phiF fa)) sp))
    (hsaved : GHolds c.σ (varSavedInput r8 r9 r18 r19 r20 r21))
    (hloaded : Code.Eval_exprLoaded c.σ.mem)
    (hlookup : Code.Env_getLoaded c.σ.mem) (hstrcmp : Code.StrcmpLoaded c.σ.mem)
    (hlo : 0x80000000 ≤ expr.toNat + 8)
    (hhi : expr.toNat + 16 ≤ 0x100000000)
    (hhtif : expr.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ expr.toNat + 8)
    (hread : read64 c.σ.mem (expr.toNat + 8) = some name.toNat)
    (w : CallerTailWindow A SL (sp + 240#64) (sp - 64#64))
    (hgap : tohostAddr + 64 ≤ sp.toNat - 64) :
    ∃ after, LookupReturnResult N A SL phiF phiC alloc exts shared s query v
      name (sp + 240#64) sp 0x80003444#64 r8 r9 r18 r19 r20 r21 c after := by
  have hchain := (get?_eq_some_iff_chain s fa query v).mp hget
  obtain ⟨f, hf⟩ := hchain.headFrame
  obtain ⟨hfa, _⟩ := Array.getElem?_eq_some_iff.mp hf
  obtain ⟨bs, entry, hc⟩ := var_call expr (BitVec.ofNat 64 (phiF fa)) sp name c
    hG hpc htick hL hloaded hlo hhi hhtif hread
  have DE : LookupData N A SL phiF phiC alloc exts shared s query name entry.σ.mem :=
    hc.memory.symm ▸ D
  obtain ⟨len, pn, hp⟩ := DE.var_prologue hfa hc hsaved
    (hc.memory.symm ▸ hlookup) w hgap
  obtain ⟨after, hr⟩ := lookup_return DE w.lookup_spill w hchain hp
    (hc.memory.symm ▸ hstrcmp) (by decide)
  refine ⟨after,
    { steps := hc.run.trans hr.steps
      good := hr.good, tick := hr.tick, loaded := hr.loaded
      pc := hr.pc, regs := hr.regs, value := hr.value, owned := hr.owned
      data := hr.data
      entryPost := ?_
      extendsMemory := by rw [← hc.memory]; exact hr.extendsMemory
      outside := fun k hk => (hr.outside k hk).trans
        (congrArg (fun m : Mem => m[k]?) hc.memory)
      output := hr.output.trans hc.output
      kept_frame := fun R hR => (hr.kept_frame R hR).trans
        (hc.caller R (by simp [varCallerKeep, hR])) }⟩
  obtain ⟨m9, hpost⟩ := hr.entryPost
  exact ⟨m9,
    { toEnvGetValuePost := hpost.toEnvGetValuePost.output_trans hc.output
      spill := fun k hk => (hpost.spill k hk).trans
        (congrArg (fun m : Mem => m[k]?) hc.memory) }⟩

#print axioms CallerTailWindow.stack_base
#print axioms CallerTailWindow.lookup_spill
#print axioms LookupData.var_prologue
#print axioms var_lookup

end Vsa.Sim.EnvGetReflected

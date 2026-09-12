import EnvGetScanAdvance
import Vsa.Sim.DeriveLoop

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim.EnvGetReflected

/-- The names already inspected contain no match. -/
structure ScanPrefixClear (f : Vsa.While.Frame) (query : String) (i : Nat) : Prop where
  earlier : ∀ j, (hj : j < f.vars.length) → j < i → (f.vars[j]'hj).1 ≠ query

theorem ScanPrefixClear.empty (f : Vsa.While.Frame) (query : String) :
    ScanPrefixClear f query 0 :=
  ⟨fun j _ hj => False.elim (Nat.not_lt_zero j hj)⟩

theorem ScanPrefixClear.succ
    {f : Vsa.While.Frame} {query : String} {i : Nat}
    (h : ScanPrefixClear f query i) (hi : i < f.vars.length)
    (hmiss : (f.vars[i]'hi).1 ≠ query) : ScanPrefixClear f query (i + 1) := by
  refine ⟨?_⟩
  intro j hj hji
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact h.earlier j hj hlt
  · have heq : j = i := by omega
    subst j
    exact hmiss

section Loop

variable (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem)

/-- Scan observations and the first-match invariant at one configuration. -/
structure ScanLoopPoint
    (g : (R : Register) → Option (RegisterType R))
    (pc ra : BitVec 64) (i : Nat) (c : Config) : Prop extends
    ScanSt g pc env name out count pn ra sp i f query N phiF phiC m0 c,
    ScanPrefixClear f query i where

/-- The generated loop is at its load head, a matching binding, or exhaustion. -/
inductive ScanLoopPosition (c : Config) : Prop where
  | head {g : (R : Register) → Option (RegisterType R)} {ra : BitVec 64} {i : Nat}
      (point : ScanLoopPoint env name out count pn sp f query N phiF phiC m0
        g 0x80002c60#64 ra i c)
      (index : i < f.vars.length)
  | hit {g : (R : Register) → Option (RegisterType R)} {i : Nat}
      (point : ScanLoopPoint env name out count pn sp f query N phiF phiC m0
        g 0x80002c70#64 0x80002c6c#64 i c)
      (index : i < f.vars.length)
      (found : (f.vars[i]'index).1 = query)
  | miss {g : (R : Register) → Option (RegisterType R)}
      (point : ScanLoopPoint env name out count pn sp f query N phiF phiC m0
        g 0x80002cc4#64 0x80002c6c#64 f.vars.length c)

/-- The loop retains the caller's frame and output at every iteration. -/
structure ScanLoopInv (before c : Config) : Prop where
  position : ScanLoopPosition env name out count pn sp f query N phiF phiC m0 c
  kept_frame : ∀ R, kept R = true → c.σ.regs.get? R = before.σ.regs.get? R
  output : c.σ.sailOutput = before.σ.sailOutput

/-- A terminal invariant rules out the load head, leaving hit or exhaustion. -/
structure ScanLoopExit (before c : Config) : Prop extends
    ScanLoopInv env name out count pn sp f query N phiF phiC m0 before c where
  exited : c.σ.regs.get? Register.PC ≠ some 0x80002c60#64

end Loop

/-- Count down remaining names only at the generated load head. -/
def scanLoopMeasure (count : BitVec 64) (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some 0x80002c60#64 then
    count.toNat - ((c.σ.regs.get? Register.x8).getD 0).toNat
  else 0

theorem scanLoopMeasure_head {count : BitVec 64} {i : Nat} {c : Config}
    (hpc : c.σ.regs.get? Register.PC = some 0x80002c60#64)
    (hidx : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i))
    (hi : i < 2^64) : scanLoopMeasure count c = count.toNat - i := by
  rw [scanLoopMeasure, if_pos hpc, hidx, Option.getD_some,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem scanLoopMeasure_exit {count pc : BitVec 64} {c : Config}
    (hpc : c.σ.regs.get? Register.PC = some pc) (hne : pc ≠ 0x80002c60#64) :
    scanLoopMeasure count c = 0 := by
  simp only [scanLoopMeasure, hpc]
  exact if_neg (fun h => hne (Option.some.inj h))

/-- A generated comparison/branch and optional back-edge preserve the loop
invariant while strictly reducing the remaining-name measure. -/
theorem scan_loop_body
    (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (before : Config) (n : Nat) :
    Triple
      (fun c => ScanLoopInv env name out count pn sp f query N phiF phiC m0 before c ∧
        c.σ.regs.get? Register.PC = some 0x80002c60#64 ∧ scanLoopMeasure count c = n)
      (fun c => ScanLoopInv env name out count pn sp f query N phiF phiC m0 before c ∧
        scanLoopMeasure count c < n) := by
  intro c ⟨hinv, hpc, hmu⟩
  cases hinv.position with
  | hit hp hi hfound =>
      have heq := Option.some.inj (hp.pc.symm.trans hpc)
      exact False.elim ((by decide : (0x80002c70#64 : BitVec 64) ≠ 0x80002c60#64) heq)
  | miss hp =>
      have heq := Option.some.inj (hp.pc.symm.trans hpc)
      exact False.elim ((by decide : (0x80002cc4#64 : BitVec 64) ≠ 0x80002c60#64) heq)
  | @head g ra i hp hi =>
      have hlen := hp.count_eq
      have hcount := count.isLt
      have hsmall : i < 2^64 := by omega
      have hhead := scanLoopMeasure_head hp.pc hp.idx0 hsmall (count := count)
      have hpositive : 0 < n := by omega
      obtain ⟨compared, taken, hdec⟩ := scan_decision g env name out count pn ra sp i
        f query N phiF phiC m0 c hp.toScanSt hi
      cases taken with
      | false =>
          have hpoint : ScanLoopPoint env name out count pn sp f query N phiF phiC m0
              g 0x80002c70#64 0x80002c6c#64 i compared :=
            { toScanSt := hdec.scan, toScanPrefixClear := hp.toScanPrefixClear }
          refine ⟨compared, hdec.steps,
            { position := .hit hpoint hi (hdec.name_match.mp rfl)
              kept_frame := fun R hR => (hdec.kept_frame R hR).trans (hinv.kept_frame R hR)
              output := hdec.output.trans hinv.output }, ?_⟩
          rw [scanLoopMeasure_exit hpoint.pc (by decide)]
          exact hpositive
      | true =>
          have hmiss : (f.vars[i]'hi).1 ≠ query := by
            intro heq
            have hbad := hdec.name_match.mpr heq
            cases hbad
          have hclear := hp.toScanPrefixClear.succ hi hmiss
          obtain ⟨advanced, exhausted, hadv⟩ := scan_advance g env name out count pn
            0x80002c6c#64 sp i f query N phiF phiC m0 compared hdec.scan hi
          have hframe : ∀ R, kept R = true →
              advanced.σ.regs.get? R = before.σ.regs.get? R := by
            intro R hR
            exact (hadv.kept_frame R hR).trans
              ((hdec.kept_frame R hR).trans (hinv.kept_frame R hR))
          have hout : advanced.σ.sailOutput = before.σ.sailOutput :=
            hadv.output.trans (hdec.output.trans hinv.output)
          cases exhausted with
          | true =>
              have heq := hadv.exhausted_iff.mp rfl
              have hpoint : ScanLoopPoint env name out count pn sp f query N phiF phiC m0
                  advanced.σ.regs.get? 0x80002cc4#64 0x80002c6c#64 (i + 1) advanced :=
                { toScanSt := hadv.scan, toScanPrefixClear := hclear }
              refine ⟨advanced, hdec.steps.trans hadv.steps,
                { position := .miss (heq ▸ hpoint), kept_frame := hframe, output := hout }, ?_⟩
              rw [scanLoopMeasure_exit hpoint.pc (by decide)]
              exact hpositive
          | false =>
              have hne : i + 1 ≠ f.vars.length := by
                intro heq
                have hbad := hadv.exhausted_iff.mpr heq
                cases hbad
              have hnext : i + 1 < f.vars.length := by omega
              have hpoint : ScanLoopPoint env name out count pn sp f query N phiF phiC m0
                  advanced.σ.regs.get? 0x80002c60#64 0x80002c6c#64 (i + 1) advanced :=
                { toScanSt := hadv.scan, toScanPrefixClear := hclear }
              refine ⟨advanced, hdec.steps.trans hadv.steps,
                { position := .head hpoint hnext, kept_frame := hframe, output := hout }, ?_⟩
              have hm := scanLoopMeasure_head hpoint.pc hpoint.idx0 (by omega) (count := count)
              omega

/-- Close the generated name scan with its caller frame at the actual exit. -/
theorem scan_loop
    (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem)
    (g : (R : Register) → Option (RegisterType R)) (ra : BitVec 64) (i : Nat)
    (c : Config)
    (hscan : ScanSt g 0x80002c60#64 env name out count pn ra sp i f query N phiF phiC m0 c)
    (hi : i < f.vars.length) (hclear : ScanPrefixClear f query i) :
    ∃ after, Steps c after ∧ ScanLoopExit env name out count pn sp f query N phiF phiC m0 c after := by
  have hloop := loopFromBody (scanLoopMeasure count)
    (scan_loop_body env name out count pn sp f query N phiF phiC m0 c)
  have hinit : ScanLoopInv env name out count pn sp f query N phiF phiC m0 c c :=
    { position := .head { toScanSt := hscan, toScanPrefixClear := hclear } hi
      kept_frame := fun _ _ => rfl
      output := rfl }
  obtain ⟨after, hsteps, hinv, hexit⟩ := hloop c hinit
  exact ⟨after, hsteps, { toScanLoopInv := hinv, exited := hexit }⟩

#print axioms ScanPrefixClear.empty
#print axioms ScanPrefixClear.succ
#print axioms scanLoopMeasure_head
#print axioms scanLoopMeasure_exit
#print axioms scan_loop_body
#print axioms scan_loop

end Vsa.Sim.EnvGetReflected

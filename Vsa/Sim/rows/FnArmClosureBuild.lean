import Vsa.Sim.rows.FnArmClosureBuildGen
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.ValueSpec
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.WriteLogNF

/-!
# `FnArmClosureBuild` — the `EX_FN` closure-build straight-line span as a `#derive_case` seg

After `malloc` returns the fresh 16-byte block in `a0` and `a3` is reloaded off the
spill slot (`ld a3,0(sp)` @0x800033d0), the `beqz a0,OOM` guard is pruned (via
`MallocContract.nonNull_of_bounded`), and the arm runs the closure-build store span

```
0x800033d8  li  a5,4          -- kind VAL_CLOSURE
0x800033dc  sd  s0,0(a0)      -- closure[0] := s0 = fn Expr node  (φf-image nothing; the ptr)
0x800033e0  sd  a3,8(a0)      -- closure[8] := a3 = φf env  (the captured environment fp)
0x800033e4  sd  a0,8(s1)      -- sret[8]   := a0 = p  (the VAL_CLOSURE payload)
0x800033e8  sw  a5,0(s1)      -- sret[0]   := 4  (the VAL_CLOSURE kind)
```

then falls through to the shared epilogue entry `0x800033ec`.  This is a pure
straight-line store span (fall-through, no terminator), so it is ONE `#derive_case`
seg carrying the whole `Steps` chain + computed end-PC (`0x800033ec`) + write-log;
the row's ONLY kernel obligation is the single `ChainOK` `decide`.  Matches the
`EnvDefSeg` idiom.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/- The seg + pin list are the GENERATED `fnArmClosureBuildSeg`/`fnArmClosureBuildL`
(`rows/FnArmClosureBuildGen.lean`, signature `(a0 s0 a3 s1)` = the block ptr, the fn
Expr node, φf env, sret) — reused by name, NOT redefined.  This file adds the
write-log reflection layer over it: the concrete log list, the writeMap chain, and
the four closure-record reads. -/

/-! ## The closure-build write-log reflected into the four record reads

`writeLog m0 log` for the closure-build seg is the ordered chain

```
writeMap4 (writeMap8 (writeMap8 (writeMap8 m0 p (sd s0)) (p+8) (sd a3)) (sret+8) (sd p)) sret (sw 4)
```

so, given the block `[p, p+16)` is disjoint from the sret window `[sret, sret+24)`
(and `p+8` disjoint from `p` internally), the four record fields read back:

* `read64 mpre p        = some s0.toNat`   (closure[0] — the fn Expr node ptr)
* `read64 mpre (p+8)    = some a3.toNat`   (closure[8] — the captured env fp φf env)
* `read64 mpre (sret+8) = some p.toNat`    (VAL_CLOSURE payload)
* `read32 mpre sret     = some 4`          (VAL_CLOSURE kind)

`fnArmClosureBuild_reads` marshals all four off the seg's computed write-log via the
`read64_writeMap8`/`read64_writeMap8_disjoint`/`read32_writeMap4` family (`ValueSpec`,
`EnvNewSpec`).  The disjointness premises `hdisj*` are the caller's geometry (the
malloc'd block never overlaps the sret box — `A.contains p 16` + the sret window). -/

/-- The closure-build write-log as its concrete 4-entry list — the FAST reflection
layer: pure seg data, no memory whnf (the fast-reflection law: reflect on the
first-order write-log, never force `writeLog` against an abstract map by `rfl`). -/
theorem fnArmClosureBuild_log_eq (s0 sret p a3 : BitVec 64) :
    (evalBlocks fnArmClosureBuildSeg
        (SegEvalState.init (fnArmClosureBuildL p s0 a3 sret) [])).log
    = [((p + sign_extend (m := 64) (0x000#12)).toNat, 8, s0),
       ((p + sign_extend (m := 64) (0x008#12)).toNat, 8, a3),
       ((sret + sign_extend (m := 64) (0x008#12)).toNat, 8, p),
       ((sret + sign_extend (m := 64) (0x000#12)).toNat, 4,
         0#64 + sign_extend (m := 64) (0x004#12))] := by rfl

/-- The reflected closure-build memory `mpre = writeLog m0 (closure-build log)`,
expressed as the ordered `writeMap` chain — via the concrete log list
(`fnArmClosureBuild_log_eq`), offset normalization, and a cheap `foldl` unfold. -/
theorem fnArmClosureBuild_mem_eq
    (s0 sret p a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    writeLog m0 (evalBlocks fnArmClosureBuildSeg
        (SegEvalState.init (fnArmClosureBuildL p s0 a3 sret) [])).log
    = writeMap4 (writeMap8 (writeMap8 (writeMap8 m0 p.toNat (sdData_val s0))
        (p + 8#64).toNat (sdData_val a3)) (sret + 8#64).toNat (sdData_val p))
        sret.toNat (swData (4#64)) := by
  rw [fnArmClosureBuild_log_eq]
  have h0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have h8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have h4 : (0#64 + sign_extend (m := 64) (0x004#12) : BitVec 64) = 4#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [h0, h8, h4, BitVec.add_zero, BitVec.add_zero]
  rfl

/-- **`fnArmClosureBuild_reads`** — the four closure-record reads off the seg's
write-log, given the malloc block `[p, p+16)` disjoint from the sret box
`[sret, sret+24)` (`hps`) and the internal offsets in-range (`hpof`). -/
theorem fnArmClosureBuild_reads
    (s0 sret p a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hpof : (p + 8#64).toNat = p.toNat + 8)
    (hsof : (sret + 8#64).toNat = sret.toNat + 8)
    -- block disjoint from sret box (both directions cover the whole [p,p+16) vs [sret,sret+24))
    (hps : p.toNat + 16 ≤ sret.toNat ∨ sret.toNat + 24 ≤ p.toNat) :
    let mpre := writeLog m0 (evalBlocks fnArmClosureBuildSeg
        (SegEvalState.init (fnArmClosureBuildL p s0 a3 sret) [])).log
    read64 mpre p.toNat = some s0.toNat ∧
    read64 mpre (p.toNat + 8) = some a3.toNat ∧
    read64 mpre (sret.toNat + 8) = some p.toNat ∧
    read32 mpre sret.toNat = some 4 := by
  intro mpre
  have hmem : mpre = writeMap4 (writeMap8 (writeMap8 (writeMap8 m0 p.toNat (sdData_val s0))
      (p + 8#64).toNat (sdData_val a3)) (sret + 8#64).toNat (sdData_val p))
      sret.toNat (swData (4#64)) := fnArmClosureBuild_mem_eq s0 sret p a3 m0
  rw [hpof, hsof] at hmem
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- read64 mpre p = s0 : p written by innermost writeMap8; all later writes disjoint
    rw [hmem]
    rw [read64_writeMap4_disjoint _ _ _ _ (by omega),
        read64_writeMap8_disjoint _ _ _ _ (by omega),
        read64_writeMap8_disjoint _ _ _ _ (by omega),
        read64_writeMap8 _ _ _, sdData_toNat]
  · -- read64 mpre (p+8) = a3 : written by the (p+8) writeMap8; later disjoint
    rw [hmem]
    rw [read64_writeMap4_disjoint _ _ _ _ (by omega),
        read64_writeMap8_disjoint _ _ _ _ (by omega),
        read64_writeMap8 _ _ _, sdData_toNat]
  · -- read64 mpre (sret+8) = p : written by the (sret+8) writeMap8; sret writeMap4 disjoint
    rw [hmem]
    rw [read64_writeMap4_disjoint _ _ _ _ (by omega),
        read64_writeMap8 _ _ _, sdData_toNat]
  · -- read32 mpre sret = 4 : the final writeMap4 at sret
    rw [hmem]
    rw [read32_writeMap4 _ _ _]
    have : (swData (4#64)).toNat = 4 := by decide
    rw [this]

#print axioms fnArmClosureBuildSeg
#print axioms fnArmClosureBuild_reads

end Vsa.Sim

import Vsa.Sim.ValuePayloadCoverage
import Vsa.Sim.EvalNegSim
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.EvalNegSim3
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.PinW
import Vsa.Sim.NotTailSites
import Vsa.Sim.LoadSitesTot
import Vsa.Sim.LoadSitesTotB
import Vsa.Sim.NegBlockProto
import Vsa.Sim.BlockTactics2
import Vsa.Sim.BlockAdapter
import Vsa.Sim.BlockLogic
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.EvalBoolSim
import Vsa.Sim.ReprCopy
import Vsa.Sim.DivSites2
import Vsa.Sim.ObsAvoid
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.ExitFootprint

/-!
# Layer 4 — M4 RECURSIVE case: `evalNotSim` (the `EvalE.not` case)

The fallthrough sibling of `neg` in the `EX_UNARY` arm. Both `.neg` and `.not`
share the arm head (`blockB_unary`, `EvalNegSim.lean`) that evaluates the operand
via the recursive `jal eval_expr`. They diverge at the post-call op-check
(`0x800035f8: beq a4,a5,0x800039ac` — TAKEN = neg; FALLTHROUGH = not).

Machine path for `.not` (`experiments/pctrace.md` + objdump):

```
800035ec: lw   a4,8(s0)        # op token
800035f0: li   a5,12           # T_MINUS = 12
800035f4: ld   a3,144(sp)      # sub-value v[0..8)  (kind dword)
800035f8: beq  a4,a5,800039ac  # NOT taken (op != 12) → fallthrough
800035fc: ld   a4,152(sp)      # v[8..16)   (payload)
80003600: ld   a5,160(sp)      # v[16..24)
80003604: addi a0,sp,64        # a0 := sp'+64 = sp-1024 (truthy arg buffer)
80003608: sd   a3,64(sp)       # copy v[0..8)  → buf
8000360c: sd   a4,72(sp)       # copy v[8..16) → buf+8
80003610: sd   a5,80(sp)       # copy v[16..24)→ buf+16
80003614: jal  value_truthy    # value_truthy(buf); ra = 0x80003618
80003618: seqz a1,a0           # a1 := (a0 == 0) = !v.truthy
8000361c: mv   a0,s1           # a0 := outer sret
80003620: jal  value_bool      # value_bool(sret, !v.truthy); ra = 0x80003624
80003624: j    800033ec        # shared epilogue → blockD_v_rec
```

`blockC_not` reproduces the whole tail (`SubEvalReturn @0x800035ec` with the
`beq` NOT taken → `PreEpilogueVD` at value `.bool (!vsub.truthy)`), threading the
24-byte header copy into the truthy arg buffer (`truthyHeaderRepr_copy_total`),
`value_truthy_header_spec`, the `seqz` bridge, and
`value_bool_spec_full`. `evalNotSim` then composes `blockA_k ≫ blockB_unary ≫
blockC_not ≫ blockD_v_rec` in the `EvalIH` motive shape, mirroring `evalNegSim`.

Conditional (like `evalNegSim`) ONLY on the `NegExtras` geometry (reused verbatim
where the fields fit, plus the NOT-tail-specific buffer geometry `NotExtras`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `Value_truthyLoaded` survives a disjoint 8-byte store / an agreement -/

/- `loaded_bool_agreeP` RELOCATED to `InterpEntry.lean` (wave 47f, `GeomFrom`);
same name/namespace. -/

/-! ## The `seqz` bridge: `!v.truthy` as a `.bool` payload

`value_truthy` returns `a0 = cond v.truthy 1 0`. `seqz a1,a0` computes
`a1 = zext (bool_to_bit (a0 <u 1)) = (a0 == 0)`. `value_bool` produces
`.bool (a1 != 0)`. We show `.bool (a1 != 0) = .bool (!v.truthy)`. -/

/-! ## Store-byte extraction for the 24-byte copy

Each of the three copy stores writes `sdData_val (sign_extend (m:=64) (b7++…++b0))`
into an 8-byte window; byte `k` of that window reads back exactly `bk` (the byte
that was loaded from the source). `sdData_val` is the identity and the `sign_extend`
of a width-64 word is the identity, so `extractLsb' (8k) 8` of the appended bytes
selects `bk`. -/
theorem sdData_sext_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 0 8 = b0 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 8 8 = b1 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 16 8 = b2 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 24 8 = b3 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 32 8 = b4 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 40 8 = b5 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 48 8 = b6 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 56 8 = b7 := by
  rw [sdData_val_id, sext_full]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
     rw [word8_toNat_recon]; omega)

/-! ## `NotExtras` — reached truthiness-buffer facts -/

/-! ## `blockC_not` — the post-call `not` tail -/

/-! ## `NotSimExtras` — the recursive-case facts beyond `EvalEntry` (mirrors `NegExtras`)

The `.not` analogue of `NegExtras` (`EvalNegSim3.lean`): the same operand-node
`ExprRepr`+geometry, the +1088 recursive headroom, the arena/code/table
disjunctions and the `EX_UNARY` slot pin — with `.not` for the AST subtree — PLUS
the two extra callee-code pins (`value_truthy`/`value_bool`) and their
disjunctions. These are
the residual-#1 program-structure facts an `EvalEntry` widening / M6 Layout would
supply; a future `blockA_k` widening + full stack-layout derivation discharges
them (exactly as for `evalNegSim`). -/

/-! ## `EvalNotSimGoal` — the `EvalE.not` projection of the simulation

In the `EvalIH` motive shape (`EvalEntry → EvalExitD`), mirroring `EvalNegSimGoal`.
The ordinary child `EvalIH` supplies the returned value header.
`NotSimExtras` supplies entry geometry and code pins. -/

end Vsa.Sim

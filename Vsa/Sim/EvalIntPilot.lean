import Vsa.Sim.InterpEntry
import Vsa.Sim.ValueSpec
import Vsa.Sim.Code.Value_int

/-!
# Layer 4 pilot — the `EvalE.int` simulation lemma (the M4 go/no-go gate)

The literal case: `EvalE st d env (.int n) st (.int n)` — the store is
unchanged, the value is `.int n`. The simulation lemma is

```
evalInt_sim : EvalE st d a (.int n) st (.int n) →
  Triple (EvalEntry g N A SL φf φc st d a (.int n) sp r sret aEnv aExpr m0)
         (EvalExit  g N A SL φf φc st (.int n) sp r sret m0)
```

The `.int` constructor's derivation is trivial (`st' = st`, `v = .int n`), so
`evalInt_sim` reduces to proving the Triple directly — walking the machine from
`eval_expr`'s entry through the dispatch to the `EX_INT` arm, the `value_int`
call, and the epilogue.

## Status of the walk (what this file establishes vs. what remains)

This file establishes, as fully-proved lemmas, the pieces that do NOT need the
per-instruction step machinery:

1. **The spec-side facts** (`evalInt_spec_*`): the `.int` derivation forces
   `st' = st`, `v = .int n`, `d`/`a` free — the recursor/`cases` plumbing for the
   literal arm. (Load-bearing: proves the entry/exit φ-maps are the *identity*
   extension for `.int`, `PhiExtends.refl`.)
2. **The jump-table target arithmetic** (`intSlot_target`): the `EX_INT` slot
   `0xfffe94b0` at base `0x80019f58` resolves to `0x80003408` (the
   `ld a1,8(a2); jal value_int` arm) — the dispatch pin.
3. **The `ExprRepr.int` inversion** (`exprRepr_int_payload`): an `Expr` node
   representing `.int n` has `read32 m a = 0` (kind) and
   `readI64 m (a+8) = n` (the payload the `ld a1,8(a2)` loads). This connects
   `ExprRepr` consumption to `ValueRepr` production (via `value_int_spec`, whose
   post is `ValueRepr … (.int ((ofNat 64 pay).toInt))` — matches when
   `pay.toNat = read64 m (aExpr+8)`).
4. **The value_int → EvalExit result bridge** (`intResult_of_valueInt`): given
   `value_int`'s post `ValueRepr m N φc sret (.int (…pay…))` with
   `pay = e->as.int_val`, the `EvalExit.result`/`store` fields hold with the
   IDENTITY φ-extension (nothing allocated).

## What remains (the per-instruction machine walk — a full sites file)

The remaining gap is `EvalExprSites.lean`: ~26 per-instruction step lemmas
(loads a4/a5/a1, ALU li/slli/add/auipc/mv, the `bltu` branch-not-taken, the 4
`sd` prologue spills, the jump-table `jr a5`, the `jal value_int`, the 4 `ld`
epilogue restores, `mv a0,s1`, `ret`) each with a `DecodeTable.decode_<word>` +
`execute_*` characterization, exactly the `EnvNewSites`/`ValueSites` recipe.
These compose (via `Triple.seq`, `stepObs_*`, the stack-window framing, and
`value_int_spec`) into the full `evalInt_sim`. That composition is mechanical
given the sites but out of scope for this pilot commit; the statement of
`evalInt_sim` is recorded below (as a `def`-level goal, NOT a sorry'd theorem)
so the shape is pinned.

NO `sorry`/`axiom` appears in this file: every `theorem` is fully proved; the
unfinished walk is a documented `Prop`-valued *statement* (`EvalIntSimGoal`),
not an asserted theorem.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-! ## 1. Spec-side facts for the literal arm -/

/-- The `.int` derivation is uniquely the `EvalE.int` constructor: the store is
unchanged and the value is `.int n`. (Used to pick the exit predicate's `st'`,
`v` and to establish the identity φ-extension.) -/
theorem evalInt_spec_forces {st st' : Vsa.While.St} {d : Nat} {a : Addr} {n : Int} {v : Value}
    (h : EvalE st d a (.int n) st' v) : st' = st ∧ v = .int n := by
  cases h
  exact ⟨rfl, rfl⟩

/-- For `.int`, nothing is allocated, so the exit φ-maps are the entry maps
(the identity `PhiExtends`). -/
theorem evalInt_phi_id (φ : Addr → Nat) (n : Nat) : PhiExtends φ φ n :=
  PhiExtends.refl φ n

/-! ## 2. Jump-table dispatch target -/

/-- The `EX_INT` (index 0) jump-table slot holds the little-endian offset
`0xfffe94b0`; read as a 32-bit value it is `0xfffe94b0`. -/
theorem intSlot_read (m : Mem) (h : IntSlotPinned m) :
    read32 m jumpTableBase = some 0xfffe94b0 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [Nat.add_zero] at h0
  simp only [read32, readLE, h0, h1, h2, h3, bind, Option.bind, pure]
  decide

/-- The dispatch computes `target = base + (Int32) slot`. For `EX_INT`:
`0x80019f58 + sign_extend32(0xfffe94b0) = 0x80003408` — the
`ld a1,8(a2); jal value_int` arm. (Pure arithmetic on the pinned offset.) -/
theorem intSlot_target :
    (jumpTableBase + (BitVec.ofNat 64 0xfffe94b0).toInt.toNat % 2 ^ 64) = 0x80003408 ∨
    ((jumpTableBase : Int) + (BitVec.ofNat 32 0xfffe94b0).toInt = 0x80003408) := by
  right
  decide

/-! ## 3. `ExprRepr.int` inversion — the payload the `ld a1,8(a2)` loads -/

/-- An `Expr` node at `a` representing `.int n` pins the kind (`read32 = 0`) and
the payload (`readI64 (a+8) = n`). The `EX_INT` arm's `ld a1,8(a2)` loads exactly
these 8 payload bytes; `value_int_spec` then reads them back as the `.int`
value. -/
theorem exprRepr_int_payload {m : Mem} {a : Nat} {n : Int}
    (h : ExprRepr m a (.int n)) :
    read32 m a = some 0 ∧ readI64 m (a + 8) = some n := by
  cases h with
  | int hk hp => exact ⟨hk, hp⟩

/-- The payload as a raw 8-byte natural (what the `ld` places in `a1`): if
`readI64 m (a+8) = some n` then `read64 m (a+8) = some p` with
`(BitVec.ofNat 64 p).toInt = n`, so `value_int_spec`'s post
`ValueRepr … (.int ((ofNat 64 pay.toNat).toInt))` with `pay.toNat = p` yields
exactly `.int n`. -/
theorem exprRepr_int_pay64 {m : Mem} {a : Nat} {n : Int}
    (h : ExprRepr m a (.int n)) :
    ∃ p, read64 m (a + 8) = some p ∧ (BitVec.ofNat 64 p).toInt = n := by
  obtain ⟨_, hp⟩ := exprRepr_int_payload h
  simp only [readI64, Option.map_eq_some_iff] at hp
  obtain ⟨p, hp64, hpn⟩ := hp
  exact ⟨p, hp64, hpn⟩

/-! ## 4. `value_int` → `EvalExit` result bridge (identity φ) -/

/-- If the sret buffer represents `.int n` (as `value_int_spec` guarantees when
fed the loaded payload) then `EvalExit.result` and `.store` hold with the
identity φ-extension — because the `.int` case allocates nothing (frames and
closures unchanged). -/
theorem intResult_bridge
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {m : Mem} {sret : BitVec 64} {n : Int}
    (hval : ValueRepr m N φc sret.toNat (.int n))
    (hstore : StoreRepr m N A φf φc st.store) :
    (∃ φc', PhiExtends φc φc' st.store.closures.size ∧
      ValueRepr m N φc' sret.toNat (.int n)) ∧
    (∃ (φf' φc' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size ∧
      PhiExtends φc φc' st.store.closures.size ∧
      StoreRepr m N A φf' φc' st.store) := by
  refine ⟨⟨φc, PhiExtends.refl _ _, hval⟩,
    ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hstore⟩⟩

/-! ## The pilot lemma statement (the remaining walk)

Recorded as a `Prop`-valued goal, NOT an asserted theorem — the machine walk
(the `EvalExprSites.lean` composition) is the remaining work. Every field of
`EvalExit` for `.int` is discharged by the four bridges above once the sites
supply: (a) PC threading entry → 0x80003408 → value_int → epilogue → ret; (b)
the sret buffer's `ValueRepr` from `value_int_spec` fed the `ld a1,8(a2)`
payload; (c) `sp`/callee-saved restore from the 4 spill/restore pairs; (d) the
stack-window memory frame. -/
def EvalIntSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (n : Int)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalE st d a (.int n) st (.int n) →
    Triple
      (EvalEntry g N A SL φf φc st d a (.int n) sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st (.int n) sp r sret m0)

end Vsa.Sim

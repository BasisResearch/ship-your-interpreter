import Vsa.RuntimeRepr
import Vsa.MemRepr
import Vsa.Alloc
import Vsa.While.StackNeed
import Vsa.Triple
import Vsa.Sim.GoodState
import Vsa.Sim.Regions
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.Code.Value_int
import Vsa.Sim.Code.Value_null
import Vsa.Sim.Code.Value_bool
import Vsa.Sim.Code.Value_str
import Vsa.Sim.MemRegion

-- discipline: allow(R7-conj-tower-def) file-level ∃ count crossed 8 by the 47i
-- RELOCATION of the landed `EvalGround`/`KindSlotPinned` layer into the entry's
-- home file; every ∃ here is a data-carrying field of a NAMED structure (the
-- WidenMeta "Prop structure cannot project data" idiom), not an anonymous tower.

/-!
# Layer 4 — the `EvalEntry`/`EvalExit` machine-side predicates for `eval_expr`

The Layer-4 simulation induction (`experiments/M4-induction-design.md`) states,
per big-step relation, a `Vsa.Logic.Triple` between an *entry* and *exit*
predicate. This file gives the **v1** predicates for the `EvalE` relation,
minimal but sufficient for the `EvalE.int` pilot (`Vsa/Sim/EvalIntPilot.lean`).

They are deliberately PARAMETRIC and documented; several fields are marked
`TODO` where the full induction (var lookup, calls, allocation) will require
more — those are noted explicitly rather than left `sorry`.

## The `eval_expr` ABI (read off `experiments/disasm.txt`, entry `0x80003164`)

```
80003164:  lw   a4,0(a2)          -- a4 = e->kind         (a2 = Expr*)
80003168:  addi sp,sp,-1088       -- 1088-byte stack frame
8000316c:  sd   s0,1072(sp)       -- spill callee-saved s0
80003170:  sd   s2,1056(sp)       --   … s2
80003174:  sd   ra,1080(sp)       --   … ra
80003178:  sd   s1,1064(sp)       --   … s1
80003180:  mv   s0,a2             -- s0 = Expr*
80003184:  mv   s2,a1             -- s2 = env
80003198:  mv   s1,a0             -- s1 = a0 = SRET BUFFER
…dispatch (jump table @ 0x80019f58, EX_INT index 0 → 0x80003408)…
```

**Convention** (confirmed): `eval_expr(Value *sret, Env *env, Expr *e)`:
* `a0 (x10)` = pointer to the caller-provided 24-byte result `Value` buffer
  (the sret buffer). The function fills `*a0`; the epilogue does `mv a0,s1`,
  returning the same pointer.
* `a1 (x11)` = machine address of the current scope (`φf` of the spec `env`).
* `a2 (x12)` = machine address of the `Expr` node (with `ExprRepr` of `e`).
* `ra (x1)`  = return address.

## Depth field (DEFERRED for `.int`)

The interpreter tracks `call_depth` in the `interp` struct (`interp.c`,
`MAX_CALL_DEPTH 1000`), read/written only on the `EX_CALL` arm
(`0x8000329c: lw a4,8(s2)` and `0x800032a8: sw a4,8(s2)` = `interp->call_depth`).
The spec threads a matching `d : Nat` (`Semantics.lean`, capped at
`maxCallDepth = 1000`).

**CONFIRMED ABI point** (from the recursive call at `0x800031bc`, which resets
`a0` and `a2` but NOT `a1`): `a1 (x11)` is the persistent **`interp*`** context
(holding `call_depth`), threaded unchanged through recursion; `mv s2,a1` saves it
callee-side. The *scope* (`env`) is reached through the interp context / the AST,
NOT passed as a raw `a1` env pointer. The `EvalEntry.a1` field below therefore
names the machine reg `aEnv` loosely — for `.int` the arm reads neither the
interp nor the env, so the distinction is invisible and v1 keeps a single ghost.
The precise `interp*`/`env` split and the `call_depth` field relation
(`read32 m (interp+8) = some d`) are wired in at the `EvalE.call` case (TODO on
the `frame`/`a1` fields).
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

/-- Machine entry PC of `eval_expr`. -/
def evalExprEntry : Nat := 0x80003164

/-- Register set preserved across `eval_expr` for the ghost frame: the RISC-V
callee-saved set (`AbiPreserved`) plus the machine-noise registers (PC/nextPC/
minstret/…). An `abbrev` so `by decide` can synthesize `Decidable` and the frame
helpers destructure it (M3 rule). -/
abbrev AbiPreservedNoise (R : Register) : Prop :=
  AbiPreserved R = true ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-! ## φ-extension order (`PhiExtends`)

Every allocation extends `φf`/`φc`; an exit predicate quantifies `∃ φf' ⊇ φf`.
`PhiExtends φ φ' n` says `φ'` agrees with `φ` on the first `n` spec addresses
(the allocated prefix at the pre-state). Composition is transitive. For the
`.int` case nothing is allocated, so the witness is the identity extension
(`PhiExtends φ φ n`, `.refl`). -/
def PhiExtends (φ φ' : Addr → Nat) (n : Nat) : Prop :=
  ∀ a, a < n → φ' a = φ a

theorem PhiExtends.refl (φ : Addr → Nat) (n : Nat) : PhiExtends φ φ n :=
  fun _ _ => rfl

theorem PhiExtends.trans {φ φ' φ'' : Addr → Nat} {n : Nat}
    (h1 : PhiExtends φ φ' n) (h2 : PhiExtends φ' φ'' n) : PhiExtends φ φ'' n :=
  fun a ha => (h2 a ha).trans (h1 a ha)

/-- Weaken the prefix bound (a wider agreement implies a narrower one). -/
theorem PhiExtends.mono {φ φ' : Addr → Nat} {n m : Nat} (hnm : n ≤ m)
    (h : PhiExtends φ φ' m) : PhiExtends φ φ' n :=
  fun a ha => h a (Nat.lt_of_lt_of_le ha hnm)

/-! ## `InterpCodeLoaded` — the reachable-code bundle

Every case of the induction needs `eval_expr`'s own code loaded, plus the code
of every function it can call. For the `.int` case that is `eval_expr` (the
dispatch + arm) and `value_int` (the callee). The full bundle grows to include
`env_new`, `env_define`, `value_*`, `eval_binary`, the string/arith helpers,
etc. Kept as a single conjunction so it threads as one hypothesis.

TODO: add the remaining callees as constructor cases come online. The
`value_int` predicate lives in `Vsa/Sim/Code/Value_int.lean` (imported by the
pilot, not here, to keep this file's import surface small). -/
def InterpCodeLoaded (m : Mem) : Prop :=
  Eval_exprLoaded m
  -- TODO ∧ Value_intLoaded m ∧ Value_nullLoaded m ∧ … (bundled at the call site
  -- in the pilot; kept out of this def so InterpEntry does not depend on the
  -- value_* code files).

/-! ## The jump-table byte-pin

The `EX_*` dispatch compiles to a `.rodata` jump table at `0x80019f58`
(`CSWTCH.18+0x30`). The table bytes are NOT part of `Eval_exprLoaded` (that pins
only the `[0x80003164, 0x80003fe0)` text). The dispatch does
`lw a5,0(table + 4*kind); jr table + a5`, so the case entry needs the four bytes
of the `kind`-th table slot pinned. For `EX_INT` (kind 0) the slot at
`0x80019f58` holds `b0 94 fe ff` (LE) = offset `0xfffe94b0`, and
`0x80019f58 + (Int32)0xfffe94b0 = 0x80003408` (the `ld a1,8(a2); jal value_int`
arm). We pin exactly that slot; wider cases pin their own slots. -/
def jumpTableBase : Nat := 0x80019f58

/-- The four bytes of the `EX_INT` (index 0) jump-table slot: `b0 94 fe ff`. -/
def IntSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 0 : Nat)]? = some (0xb0 : BitVec 8) ∧
  m[(jumpTableBase + 1 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 2 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 3 : Nat)]? = some (0xff : BitVec 8)

/-! ## The null/bool/str callee pins (wave 47f — `GeomFrom`)

The three sibling leaf callees' code windows and jump-table slots, RELOCATED
here from `EvalStrSim`/`EvalBoolSim`/`EvalNullSim` (same names, same namespace —
zero consumer changes) so `EvalEntry` can carry them: the `hNull`/`hBool`/`hStr`
residuals need them at the ENTRY config (`evalentry-missing-nbs-callee-geom`,
machine-checked in `experiments/fleet/obstructions/
B1_reseat_footprint_verdict.lean`).  The `*_slot_kindPinned` bridge theorems
stay beside the sims (they mention `KindSlotPinned`, defined above this file's
layer). -/

/-- The `EX_STR` (tag 1) jump-table slot pin: `jumpTableBase + 4` holds
`bc 94 fe ff` (LE offset `0xfffe94bc` → arm `0x80003414`). -/
def StrSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 4 : Nat)]? = some (0xbc : BitVec 8) ∧
  m[(jumpTableBase + 5 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 6 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 7 : Nat)]? = some (0xff : BitVec 8)

/-- The `EX_BOOL` (tag 2) jump-table slot pin: `jumpTableBase + 8` holds
`c8 94 fe ff` (LE offset `0xfffe94c8` → arm `0x80003420`). -/
def BoolSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 8 : Nat)]? = some (0xc8 : BitVec 8) ∧
  m[(jumpTableBase + 9 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 10 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 11 : Nat)]? = some (0xff : BitVec 8)

/-- The `EX_NULL` (tag 3) jump-table slot pin: `jumpTableBase + 12` holds
`d4 94 fe ff` (LE offset `0xfffe94d4` → arm `0x8000342c`). -/
def NullSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 12 : Nat)]? = some (0xd4 : BitVec 8) ∧
  m[(jumpTableBase + 13 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 14 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 15 : Nat)]? = some (0xff : BitVec 8)

/-- `Value_nullLoaded` survives an agreement on `value_null`'s code region
`[0x800027ec, 0x800027f8)` (RELOCATED from `EvalCallNative2`). -/
theorem loaded_null_agreeP (m m' : Mem)
    (ha : ∀ a, (0x800027ec ≤ a ∧ a < 0x800027f8) → m[a]? = m'[a]?)
    (h : Value_nullLoaded m) : Value_nullLoaded m' := by
  simp only [Value_nullLoaded, Vsa.Sim.Code.value_nullChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [← ha _ (by omega)]; simp_all only [])

/-- `Value_boolLoaded` survives an agreement on `value_bool`'s code region
`[0x800027f8, 0x8000280c)` (RELOCATED from `EvalNotSim`). -/
theorem loaded_bool_agreeP (m m' : Mem)
    (ha : ∀ a, (0x800027f8 ≤ a ∧ a < 0x8000280c) → m[a]? = m'[a]?)
    (h : Value_boolLoaded m) : Value_boolLoaded m' := by
  simp only [Value_boolLoaded, Vsa.Sim.Code.value_boolChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [← ha _ (by omega)]; simp_all only [])

/-- `Value_strLoaded` survives an agreement on `value_str`'s code region
`[0x8000281c, 0x8000282c)`. -/
theorem loaded_str_agreeP (m m' : Mem)
    (ha : ∀ a, (0x8000281c ≤ a ∧ a < 0x8000282c) → m[a]? = m'[a]?)
    (h : Value_strLoaded m) : Value_strLoaded m' := by
  simp only [Value_strLoaded, Vsa.Sim.Code.value_strChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [← ha _ (by omega)]; simp_all only [])

/-- **`NBSPins` — the null/bool/str callee byte pins** (the `GeomFrom` supplier
layer's memory half): the three sibling leaf callees' code windows loaded and
their jump-table slots (tags 1-3) pinned.  Named-field structure (gate shape);
carried by `EvalEntry.nbs_pins` and transported across stack-confined writes by
`NBSPins.survive_stack`. -/
structure NBSPins (m : Mem) : Prop where
  null_code : Value_nullLoaded m
  bool_code : Value_boolLoaded m
  str_code : Value_strLoaded m
  null_slot : NullSlotPinned m
  bool_slot : BoolSlotPinned m
  str_slot : StrSlotPinned m

/-- `NBSPins` transport: agreement on the value_* text window
`[0x800027ec, 0x8000282c)` and the tag-1..3 table slots `[0x80019f5c, 0x80019f68)`
carries every pin. -/
theorem NBSPins.transport {m m' : Mem} (h : NBSPins m)
    (htext : ∀ a, (0x800027ec ≤ a ∧ a < 0x8000282c) → m[a]? = m'[a]?)
    (htable : ∀ a, (0x80019f5c ≤ a ∧ a < 0x80019f68) → m[a]? = m'[a]?) :
    NBSPins m' where
  null_code := loaded_null_agreeP m m' (fun a ha => htext a (by omega)) h.null_code
  bool_code := loaded_bool_agreeP m m' (fun a ha => htext a (by omega)) h.bool_code
  str_code := loaded_str_agreeP m m' (fun a ha => htext a (by omega)) h.str_code
  null_slot := by
    obtain ⟨p0, p1, p2, p3⟩ := h.null_slot
    exact ⟨(htable _ (by simp only [jumpTableBase]; omega)).symm.trans p0,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p1,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p2,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p3⟩
  bool_slot := by
    obtain ⟨p0, p1, p2, p3⟩ := h.bool_slot
    exact ⟨(htable _ (by simp only [jumpTableBase]; omega)).symm.trans p0,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p1,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p2,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p3⟩
  str_slot := by
    obtain ⟨p0, p1, p2, p3⟩ := h.str_slot
    exact ⟨(htable _ (by simp only [jumpTableBase]; omega)).symm.trans p0,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p1,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p2,
      (htable _ (by simp only [jumpTableBase]; omega)).symm.trans p3⟩

/-- `NBSPins` survives any memory change confined to the stack scribble
`[SL.lo, sp)`, given the (widened) text/table stack-disjointness the entry
carries.  The workhorse at every entry→child-entry seam: the pre-call writes
between two entries are stack-confined. -/
theorem NBSPins.survive_stack {SL : StackLayout} {sp : BitVec 64} {m m' : Mem}
    (h : NBSPins m)
    (hvi : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec)
    (htb : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (hag : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → m[k]? = m'[k]?) :
    NBSPins m' :=
  h.transport
    (fun a ha => hag a (by rcases hvi with hv | hv <;> omega))
    (fun a ha => hag a (by rcases htb with ht | ht <;> omega))

/-! ## `KindSlotPinned` — the per-kind jump-table slot pin (dispatch coupling)

RELOCATED from `EvalSimCommon.lean` (wave 47i — the `EvalGround` bundle below
needs it; same name/namespace, zero consumer changes).  The `EX_*` dispatch
reads a 4-byte offset from the `.rodata` jump table at
`jumpTableBase = 0x80019f58`, slot `k` living at `jumpTableBase + 4*k`, then
jumps to `jumpTableBase + (Int32)offset`. -/
def KindSlotPinned (k : Nat) (armPC : BitVec 64) (m : Mem) : Prop :=
  ∃ t0 t1 t2 t3 : BitVec 8,
    m[(jumpTableBase + 4 * k + 0 : Nat)]? = some t0 ∧
    m[(jumpTableBase + 4 * k + 1 : Nat)]? = some t1 ∧
    m[(jumpTableBase + 4 * k + 2 : Nat)]? = some t2 ∧
    m[(jumpTableBase + 4 * k + 3 : Nat)]? = some t3 ∧
    (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
      + BitVec.ofNat 64 jumpTableBase) = armPC

/-! ## `EvalGround` — the batched entry-ground bundle (wave 47h/47i, audit N1/N3/N4/N5)

RELOCATED from `EntryGround.lean` at insertion time (47i): `EvalEntry.ground`
needs these BELOW the entry structure.  Same names/namespace — zero consumer
changes.  See `experiments/entry-needs-audit.md` §C for the design. -/

/-- N1 — the full eval jump-table pin bundle (tags 0-10).  Arm PCs are the
generated table (`LayoutJumpTableGen` header); the per-wave trickle fields
(`int_slot` tag 0, `nbs_pins` slots 1-3) stay for their landed consumers. -/
structure KindTablePins (m : Mem) : Prop where
  slot0 : KindSlotPinned 0 (0x80003408#64) m   -- EX_INT
  slot1 : KindSlotPinned 1 (0x80003414#64) m   -- EX_STR
  slot2 : KindSlotPinned 2 (0x80003420#64) m   -- EX_BOOL
  slot3 : KindSlotPinned 3 (0x8000342c#64) m   -- EX_NULL
  slot4 : KindSlotPinned 4 (0x80003434#64) m   -- EX_VAR
  slot5 : KindSlotPinned 5 (0x8000347c#64) m   -- EX_ASSIGN
  slot6 : KindSlotPinned 6 (0x800034e8#64) m   -- EX_BINARY
  slot7 : KindSlotPinned 7 (0x8000355c#64) m   -- EX_LOGICAL
  slot8 : KindSlotPinned 8 (0x800035e0#64) m   -- EX_UNARY
  slot9 : KindSlotPinned 9 (0x800031b0#64) m   -- EX_CALL
  slot10 : KindSlotPinned 10 (0x800033c4#64) m -- EX_FN

/-- One slot's pin survives agreement on its own 4-byte window. -/
theorem kindSlotPinned_agree {k : Nat} {armPC : BitVec 64} {m m' : Mem}
    (h : KindSlotPinned k armPC m)
    (ha : ∀ a, jumpTableBase + 4 * k ≤ a → a < jumpTableBase + 4 * k + 4 →
      m[a]? = m'[a]?) :
    KindSlotPinned k armPC m' := by
  obtain ⟨t0, t1, t2, t3, h0, h1, h2, h3, he⟩ := h
  exact ⟨t0, t1, t2, t3,
    (ha _ (by omega) (by omega)).symm.trans h0,
    (ha _ (by omega) (by omega)).symm.trans h1,
    (ha _ (by omega) (by omega)).symm.trans h2,
    (ha _ (by omega) (by omega)).symm.trans h3, he⟩

/-- `KindTablePins` transport: agreement on the whole 44-byte table window. -/
theorem KindTablePins.transport {m m' : Mem} (h : KindTablePins m)
    (ha : ∀ a, jumpTableBase ≤ a → a < jumpTableBase + 44 → m[a]? = m'[a]?) :
    KindTablePins m' where
  slot0 := kindSlotPinned_agree h.slot0 (fun a h1 h2 => ha a (by omega) (by omega))
  slot1 := kindSlotPinned_agree h.slot1 (fun a h1 h2 => ha a (by omega) (by omega))
  slot2 := kindSlotPinned_agree h.slot2 (fun a h1 h2 => ha a (by omega) (by omega))
  slot3 := kindSlotPinned_agree h.slot3 (fun a h1 h2 => ha a (by omega) (by omega))
  slot4 := kindSlotPinned_agree h.slot4 (fun a h1 h2 => ha a (by omega) (by omega))
  slot5 := kindSlotPinned_agree h.slot5 (fun a h1 h2 => ha a (by omega) (by omega))
  slot6 := kindSlotPinned_agree h.slot6 (fun a h1 h2 => ha a (by omega) (by omega))
  slot7 := kindSlotPinned_agree h.slot7 (fun a h1 h2 => ha a (by omega) (by omega))
  slot8 := kindSlotPinned_agree h.slot8 (fun a h1 h2 => ha a (by omega) (by omega))
  slot9 := kindSlotPinned_agree h.slot9 (fun a h1 h2 => ha a (by omega) (by omega))
  slot10 := kindSlotPinned_agree h.slot10 (fun a h1 h2 => ha a (by omega) (by omega))

/-- N3 — the AST region for the expression tree at `aExpr`: nodes hereditarily
in `[lo, hi)` (`MemRegion.ExprIn`), region in RAM above HTIF, disjoint from the
WHOLE stack region, from the result buffer, and from the arena. -/
structure AstRegionSpec (m : Mem) (SL : StackLayout) (A : Arena)
    (sret aExpr : Nat) (e : Vsa.While.Expr) (lo hi : Nat) : Prop where
  nodes : ExprIn m lo hi aExpr e
  lo_ram : 0x80000000 ≤ lo
  hi_ram : hi ≤ 0x100000000
  win : tohostAddr + 16 ≤ lo
  stack_disjoint : hi ≤ SL.lo ∨ SL.hi ≤ lo
  sret_disjoint : hi ≤ sret ∨ sret + 24 ≤ lo
  arena_disjoint : hi ≤ A.lo ∨ A.hi ≤ lo

/-- The ∃-packaged eval AST-region pin (a `Prop` structure cannot carry the
`lo`/`hi` data fields — 47g `StrPayloadIn` precedent). -/
structure AstRegionPins (m : Mem) (SL : StackLayout) (A : Arena)
    (sret aExpr : Nat) (e : Vsa.While.Expr) : Prop where
  region : ∃ lo hi, AstRegionSpec m SL A sret aExpr e lo hi

/-- `AstRegionSpec` transports along agreement on `[lo, hi)` (only `nodes`
touches `m`; `exprIn_agreeP` carries it). -/
theorem AstRegionSpec.transport {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sret aExpr : Nat} {e : Vsa.While.Expr} {lo hi : Nat}
    (h : AstRegionSpec m SL A sret aExpr e lo hi)
    (ha : ∀ a, lo ≤ a → a < hi → m[a]? = m'[a]?) :
    AstRegionSpec m' SL A sret aExpr e lo hi where
  nodes := exprIn_agreeP (fun a hp => ha a hp.1 hp.2) e h.nodes
  lo_ram := h.lo_ram
  hi_ram := h.hi_ram
  win := h.win
  stack_disjoint := h.stack_disjoint
  sret_disjoint := h.sret_disjoint
  arena_disjoint := h.arena_disjoint

/-- **The complete eval entry-ground bundle** (audit classes N1/N3/N4/N5).
Inserted as `EvalEntry.ground` (47i); transported by `survive_stack`; children
by `ExprIn` projection. -/
structure EvalGround (m : Mem) (SL : StackLayout) (A : Arena)
    (sp sret : BitVec 64) (aExpr : Nat) (e : Vsa.While.Expr) : Prop where
  table : KindTablePins m
  ast : AstRegionPins m SL A sret.toNat aExpr e
  arena_stack : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  arena_vi : A.hi ≤ 0x800027ec ∨ 0x8000282c ≤ A.lo
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  sret_table_disjoint : sret.toNat + 24 ≤ 0x80019f58 ∨ 0x80019f58 + 44 ≤ sret.toNat

/-- **`EvalGround` survives any memory change confined to the stack scribble
`[SL.lo, sp)` ∪ the sret window** — the standard entry→child-entry write
footprint.  Needs the entry's whole-table stack disjointness (the 47f
`table_stack_disjoint` literal) for the table half; the AST region and the
literals are self-contained. -/
theorem EvalGround.survive_stack {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Vsa.While.Expr}
    (h : EvalGround m SL A sp sret aExpr e)
    (htb : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (hsp : sp.toNat ≤ SL.hi)
    (hag : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
      ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → m[k]? = m'[k]?) :
    EvalGround m' SL A sp sret aExpr e where
  table := h.table.transport (fun a h1 h2 => by
    have hj : jumpTableBase = 0x80019f58 := rfl
    refine hag a (fun hcon => ?_) (fun hcon => ?_)
    · rcases htb with ht | ht <;> omega
    · rcases h.sret_table_disjoint with hs | hs <;> omega)
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    refine ⟨lo, hi, spec.transport (fun a h1 h2 => ?_)⟩
    refine hag a (fun hcon => ?_) (fun hcon => ?_)
    · rcases spec.stack_disjoint with hs | hs
      · omega
      · have := h.sret_inSL; omega
    · rcases spec.sret_disjoint with hs | hs <;> omega⟩
  arena_stack := h.arena_stack
  arena_code := h.arena_code
  arena_vi := h.arena_vi
  sret_inSL := h.sret_inSL
  sret_table_disjoint := h.sret_table_disjoint

/-! ## `EvalEntry` — the machine precondition at `eval_expr`'s entry PC

Parameters (ghosts, ∀-bound in the simulation lemma):
* `g`   — blanket register ghost frame (`M3` discipline): every callee-preserved
  register reads back to `g R` (ties to the caller's entry state).
* `N`   — native-function addresses; `A` — heap arena; `SL` — stack region;
  `φf`/`φc` — spec↔machine correspondence maps.
* `st`  — the spec pre-state (`St`); `d` — the (capped) call depth; `a` — the
  spec scope `Addr`; `e` — the expression being evaluated.
* `sp`  — entry stack pointer; `r` — return address; `sret` — the result-buffer
  machine address; `aEnv` — machine address of the scope (`φf a`) — for `.int`,
  the arm reads neither `env` nor `interp`, so this is a ghost only; `aExpr` —
  machine address of the `Expr` node.
* `m0`  — the pinned pre-memory (for the framed exit clause). -/
structure EvalEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : St) (d : Nat) (a : Addr) (e : Expr)
    (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where
  /-- All the pinned control state (M-mode, Bare, interrupts dead, …). -/
  good : GoodState c.σ
  /-- Tick parity invariant (`M3`): the caller does not know the tick counter. -/
  tick : c.tick < 2
  /-- PC at `eval_expr`'s entry. -/
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry)
  /-- ABI arg 0: the sret buffer. -/
  a0 : c.σ.regs.get? Register.x10 = some sret
  /-- ABI arg 1: `interp*` / env machine addr (unused by `.int`). -/
  a1 : c.σ.regs.get? Register.x11 = some aEnv
  /-- ABI arg 2: the `Expr` node address. -/
  a2 : c.σ.regs.get? Register.x12 = some aExpr
  /-- Return address. -/
  ra : c.σ.regs.get? Register.x1 = some r
  /-- Return address 4-aligned (needed by the epilogue `ret`). -/
  ra_align : r.toNat % 4 = 0
  /-- Entry stack pointer. -/
  spReg : c.σ.regs.get? Register.x2 = some sp
  /-- `sp` is a good C stack pointer with 1088 + callee headroom. -/
  stackOK : StackOK SL sp (1088 + 1088)
  /-- **ITEM ZERO B1 (recursion-sound budget).** `sp` carries enough headroom
  for THIS node's structural need plus every remaining call level's budget plus
  the callee-`value_*` frame (`1088`). This is the recursion-sound replacement
  for the constant `stackOK`: a recursive child (`eval_expr` at `sp - 1088`)
  derives its own `stackBudget` from this one, because
  `e.stackNeed = evalFrame + child.stackNeed` and `evalFrame = 1088`. The old
  `stackOK` is kept and `stackBudget ⇒ stackOK` via `StackOK.mono`
  (`e.stackNeed ≥ 1088`). -/
  stackBudget : StackOK SL sp
    (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  /-- **ITEM ZERO B1.** Every `.fn` literal reachable in `e` has a body fitting
  the per-call budget — so any closure this expression allocates seeds a
  budget-fitting `StoreBodiesBound`. -/
  expr_bodies : Expr.bodiesBound Vsa.While.perCallBudget e = true
  /-- **ITEM ZERO B1.** Every closure already in the store fits the per-call
  budget — so a recursive `Call.closure` body executes within one budget level.
  Preserved by `define`/`allocFrame` (no new closure) and by `allocClosure`
  fed a `.fn`-bounded body. -/
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  /-- `minstret` present (`readReg` must not throw). -/
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  /-- Machine memory is the pinned `m0`. -/
  mem : c.σ.mem = m0
  /-- `eval_expr` (and, at the call site in the pilot, its callees) loaded. -/
  code : InterpCodeLoaded c.σ.mem
  /-- The `Expr` node at `aExpr` represents `e`. -/
  expr : ExprRepr c.σ.mem aExpr.toNat e
  /-- The whole spec store is represented (frames + closures) — needed by every
  arm that dereferences the environment; for `.int` it is carried through
  unchanged. -/
  store : StoreRepr c.σ.mem N A φf φc st.store
  /-- **`StoreRepr` survives any memory change confined to the FULL stack region
  `[SL.lo, SL.hi)` ∪ the sret buffer `[sret, sret+24)`.** This is the abstraction
  of the arena/AST-disjointness footprint reasoning (the represented
  frames/closures and their name/value strings live in the arena and AST regions,
  both disjoint from the C stack and the caller's result buffer).
  **WAVE 47e (`EntryStackSurv`) AMENDMENT**: footprint widened from `[SL.lo, sp)`
  to `[SL.lo, SL.hi)` — the recursive motive's `EvalExitD` survival clause is
  fixed at `stackFoot SL = [SL.lo, SL.hi)`, and the caller strip `[sp, SL.hi)`
  was covered by NOTHING (machine-checked verdict:
  `experiments/fleet/obstructions/B1_reseat_footprint_verdict.lean`).  The old
  `sp`-window form is recovered by `EvalEntry.store_survives_sp` (one mono
  lemma); construction sites supply the wider fact (the store footprint is
  disjoint from the WHOLE stack region, not just the scribbled prefix). -/
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
      c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  /-- Console output correspondence. -/
  out : OutRepr c.σ st
  /-- The blanket ghost frame. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- **The `eval_expr` code region is disjoint from the stack region** the
  function scribbles (`[SL.lo, sp)`). Text and C stack never overlap; this pins
  it so the prologue `sd` spills (and the `value_int` sret writes, both inside
  `[SL.lo, sp)` ∪ sret buffer) leave `eval_expr`'s code loaded.
  (v1→v2 field added by the `EvalE.int` walk: the survival of `Eval_exprLoaded`
  across the frame spills needs code∩stack = ∅.) -/
  code_stack_disjoint : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  /-- **The `Expr` node is disjoint from the stack region.** The `.int` arm reads
  `read32 aExpr` (kind) and `readI64 (aExpr+8)` (payload); both survive the frame
  spills because the AST lives outside `[SL.lo, sp)`. (v1→v2 field.) -/
  expr_stack_disjoint : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  /-- **The `Expr` node is an 8-aligned 16-byte slot in RAM above HTIF.** The
  `.int` arm's `lw a4,0(a2)`/`lwu a5,0(a2)` (kind, 4-aligned) and `ld a1,8(a2)`
  (payload, 8-aligned) need these load-region facts. (v1→v2 field.) -/
  expr_align : aExpr.toNat % 8 = 0
  expr_ram : 0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000
  expr_win : tohostAddr + 16 ≤ aExpr.toNat
  /-- **The sret buffer is a proper 24-byte `Value` slot**, 8-aligned, in RAM,
  above the HTIF window, disjoint from `value_int`'s code `[0x8000280c, 0x8000281c)`
  and from the stack region `[SL.lo, sp)`. This is exactly `value_int`'s
  `IntRegion` plus the stack-disjointness needed to keep the spills and the sret
  writes from interfering. (v1→v2 field.) -/
  sret_align : sret.toNat % 8 = 0
  sret_ram : 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000
  sret_win : tohostAddr + 16 ≤ sret.toNat
  /-- **WAVE 47f (`GeomFrom`) WIDENING**: the sret buffer is disjoint from the
  WHOLE `value_null`≫`value_bool`≫`value_int`≫`value_str` text
  `[0x800027ec, 0x8000282c)` (was: the `value_int` window `[0x8000280c,
  0x8000281c)` only).  The null/bool/str leaf residuals need their own callee
  windows; the four windows are contiguous, so ONE widened literal serves all.
  Strictly stronger — the old int-window consumers close by `omega`. -/
  sret_vicode_disjoint : sret.toNat + 24 ≤ 0x800027ec ∨ 0x8000282c ≤ sret.toNat
  sret_stack_disjoint : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  /-- The sret buffer is disjoint from `eval_expr`'s code region `[0x80003164,
  0x80003fe0)`. Needed so `value_int`'s sret write leaves `Eval_exprLoaded` intact
  (the shared epilogue reads code after the callee returns). (v2 field.) -/
  sret_evalcode_disjoint : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  /-- The `value_*` leaf-callee text `[0x800027ec, 0x8000282c)` is disjoint from
  the stack region — needed so the prologue spills keep `Value_intLoaded` (and,
  since wave 47f, the sibling `Value_{null,bool,str}Loaded` pins).
  **WAVE 47f WIDENING**: was the `value_int` window `[0x8000280c, 0x8000281c)`
  only; strictly stronger, old consumers close by `omega`. (v1→v2 field.) -/
  vicode_stack_disjoint : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec
  /-- **The stack region is in RAM and above the HTIF window.** The prologue
  `sd` spills (targets in `[SL.lo, sp) ⊆ RAM`, above `tohost`) need these to pass
  the load/store region checks. (v1→v2 field.) -/
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  /-- **`value_int` is loaded** (the `.int` callee). Bundled here (rather than in
  `InterpCodeLoaded`, which stays import-light) so the pilot's `jal value_int`
  can discharge the callee precondition. (v1→v2 field.) -/
  value_int_code : Value_intLoaded c.σ.mem
  /-- **The `EX_INT` jump-table slot is pinned** (`0x80019f58` holds `0xfffe94b0`
  LE). The dispatch `lw a5,0(a5); add a5,a5,a4; jr a5` reads this slot; it is in
  `.rodata`, not part of `Eval_exprLoaded`. `IntSlotPinned` also survives the frame
  spills (the table is at `0x80019f58`, disjoint from `[SL.lo, sp)` since the table
  is below the stack). (v1→v2 field.) -/
  int_slot : IntSlotPinned c.σ.mem
  /-- The WHOLE dispatch jump table `[0x80019f58, 0x80019f84)` (11 × 4-byte
  slots) is disjoint from the stack region (so the slot pins survive the
  spills).  **WAVE 47f WIDENING**: was the tag-0 slot `+4` only; the
  null/bool/str residuals need slots 1-3; strictly stronger, old consumers
  close by `omega`. -/
  table_stack_disjoint : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58
  /-- **The null/bool/str leaf-callee pins** (wave 47f, the `GeomFrom` supplier
  layer): `value_null`/`value_bool`/`value_str` code loaded + jump-table slots
  1-3 pinned.  Together with the widened `sret_vicode_disjoint`/
  `vicode_stack_disjoint`/`table_stack_disjoint` this closes the
  `evalentry-missing-nbs-callee-geom` gap for `hNull`/`hBool` (and the
  code-geometry half of `hStr`).  Child entries transport it via
  `NBSPins.survive_stack` (pre-call writes are stack-confined). -/
  nbs_pins : NBSPins c.σ.mem
  /-- **The batched entry-ground bundle** (wave 47i insertion — audit
  `experiments/entry-needs-audit.md` §C/§D): full jump-table pins (N1), the
  hereditary AST region (N3), arena geometry (N4), sret whole-stack membership
  (N5).  Children transport it via `EvalGround.survive_stack` + `ExprIn`
  projection; top-level supply = the M6 image (`kindTablePins_of_bytes`) + the
  parse-arena Layout fact. -/
  ground : EvalGround c.σ.mem SL A sp sret aExpr.toNat e
  /-- **The spilled callee-saved registers `s0`(x8), `s1`(x9), `s2`(x18) are
  defined** at entry (the prologue `sd s0/s1/s2` requires their `rs2` reads not to
  throw). GoodState pins control registers but not GPRs, so this is stated here;
  the ghost frame ties them to `g`, so the epilogue restores each to its entry
  value. (v1→v2 field.) -/
  spill_defined : (∃ v, c.σ.regs.get? Register.x8 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x9 = some v) ∧ (∃ v, c.σ.regs.get? Register.x18 = some v)
  /-- **`a3`(x13) is defined at entry.** `x13`/`a3` is a caller-save temp NOT
  written across the prologue+dispatch span `0x80003164→0x800034e8`; the binary
  arm (`blockB_binary`, `EvalBinSim.lean`) reads it at arm entry as the env arg
  and SPILLS it (`sd a3,0(sp)`) for the RIGHT sub-call. `blockA_k` threads it
  through untouched and emits `∃w, c'.x13 = some w` as its 3rd output, which the
  binary/unary arm bridges consume to discharge `BinArmExtras.x13_pres` /
  `EvalArmHeadExtras.x13_pres` (CURE A of the bin/eq interlock wave, wave 48h).
  `GoodState` pins control registers but not GPRs, so this is stated here. -/
  x13_defined : ∃ v, c.σ.regs.get? Register.x13 = some v
  -- TODO(call): a `call_depth` field relation `read32 m (interp+8) = some d`
  --   and the `interp*` split from `env` (a1 is `interp*`; env is a separate
  --   arg the C source passes — re-derive which machine reg holds the env for
  --   the recursive `eval_expr` calls: the EX_BINARY/EX_CALL arms reload it).
  -- TODO(alloc): an `AInv`/arena-budget field (`MallocContract`) for arms that
  --   allocate (EX_FN closure, EX_CALL frame). `.int` allocates nothing.

/-- **The `sp`-window form of `store_survives`** (the pre-amendment field, ONE
mono lemma): `[SL.lo, sp) ⊆ [SL.lo, SL.hi)` by `stackOK`, so an agreement
witness outside the small window a fortiori feeds the widened field.  Use sites
that thread the survival into an `sp`-window interface (the `blockA_k` pre
tower and its clones) consume THIS, never re-derive. -/
theorem EvalEntry.store_survives_sp
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : St} {d : Nat} {a : Addr} {e : Expr}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d a e sp r sret aEnv aExpr m0 c) :
    ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store :=
  fun m' h => hc.store_survives m'
    (fun k hk hr => h k
      (fun hcon => hk ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hc.stackOK.2.1⟩) hr)

/-! ### Narrow (pre-47f) forms of the widened geometry literals — mono lemmas

Consumers that fed the old int-window literals structurally (`exact
hc.sret_vicode_disjoint` and friends) switch to these one-token forms. -/

theorem EvalEntry.sret_vicode_disjoint_int
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : St} {d : Nat} {a : Addr} {e : Expr}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d a e sp r sret aEnv aExpr m0 c) :
    sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat := by
  rcases hc.sret_vicode_disjoint with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem EvalEntry.vicode_stack_disjoint_int
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : St} {d : Nat} {a : Addr} {e : Expr}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d a e sp r sret aEnv aExpr m0 c) :
    (0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c := by
  rcases hc.vicode_stack_disjoint with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem EvalEntry.table_stack_disjoint_int
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : St} {d : Nat} {a : Addr} {e : Expr}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d a e sp r sret aEnv aExpr m0 c) :
    (0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 := by
  rcases hc.table_stack_disjoint with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-! ## `EvalExit` — the machine postcondition at the return PC

The sret buffer holds `ValueRepr` of the produced value; the store is
re-represented for `st'.store` with EXTENDED φ-maps; callee-saved registers and
`sp` are restored; memory outside the arena/stack window is framed to `m0`. -/
structure EvalExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)          -- the ENTRY maps
    (nf nc : Nat)                 -- the ENTRY agreement sizes (frames/closures)
    (st' : St) (v : Value)
    (sp r sret : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where
  /-- Control state re-established. -/
  good : GoodState c.σ
  /-- Tick parity still `< 2` (the caller keeps stepping). -/
  tick : c.tick < 2
  /-- PC at the return target (bit-0-cleared `r`, the `ret` semantics). -/
  pc : c.σ.regs.get? Register.PC =
    some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1)
  /-- Result register: `mv a0,s1` returns the sret buffer pointer. -/
  a0 : c.σ.regs.get? Register.x10 = some sret
  /-- Return address preserved. -/
  ra : c.σ.regs.get? Register.x1 = some r
  /-- `sp` restored to entry. -/
  spReg : c.σ.regs.get? Register.x2 = some sp
  /-- `minstret` present. -/
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  /-- **The Layer-2 result**: the sret buffer represents the spec value `v`.
  (`φc'` existential extension is exposed via the `store` field below; the raw
  `ValueRepr` uses the entry `φc` when `v` is not a fresh closure — true for
  `.int`.) -/
  result : ∃ φc', PhiExtends φc φc' nc ∧
    ValueRepr c.σ.mem N φc' sret.toNat v
  /-- **The store is re-represented** for `st'.store` with extended maps. -/
  store : ∃ (φf' φc' : Addr → Nat),
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store
  /-- Console output correspondence for `st'`. -/
  out : OutRepr c.σ st'
  /-- The blanket ghost frame: every callee-preserved register is restored to
  its entry value `g R` (this is how `s0`/`sp`/… survive). -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- Memory outside the arena and the stack window `[SL.lo, sp)` is unchanged
  from `m0` (the `env_new`/malloc-post framing shape). Arms that store into the
  heap (allocations) widen this to the arena; `.int` writes only the sret buffer
  (in the caller's frame) and its own spill window. -/
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) →
    (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ c.σ.mem[a]? = m0[a]?
  -- TODO(alloc): the arena side of the frame becomes a described extension for
  --   EX_FN/EX_CALL; `.int` leaves the arena untouched (identity φ).

end Vsa.Sim

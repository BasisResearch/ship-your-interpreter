import Vsa.Sim.NegBlockProto
import Vsa.Sim.EvalNegSim
import Vsa.Triple

/-!
# Stage A0 — neg block lemmas as `Triple`s + a `seq`/`conseq` compose demo

Layer 1 (`Vsa/Triple.lean`) already gives the program logic
`Triple P Q := ∀ c, P c → ∃ c', Steps c c' ∧ Q c'` over `Config = ⟨σ, tick,
steps⟩`, with `seq`, `conseq`, … proven. `value_int_spec` is already a `Triple`
(its `int_pre`/`int_post` are the template used here).

This file restates the three neg block lemmas from `NegBlockProto.lean` —
`neg_prologue_block`, `neg_loadstore_full`, `neg_tail_block` — as `Triple`s.
Each block's entry pins/tick/memory become a `…Pre : … → Config → Prop`; its
exit pins/tick/memory/frame become a `…Post`. Following the Layer-1 design
(doc-comment at the top of `Vsa/Triple.lean`), framing is **not** a rule: the
register frame and memory survival ride *inside* the postcondition, exactly as
`int_post` does. `conseq` threads them at seams.

The wrapper proofs are near-mechanical: `intro c hpre; obtain … := hpre; obtain
… := <block lemma> …; exact ⟨…⟩`. The `Steps` witness is the block lemma's own
`Steps` (with `c' := ⟨σ', i', c.steps + blen⟩`).

The compose demo `neg_prologue_loadstore_triple` chains the prologue and
load/store triples via `Triple.seq`, with a `Triple.conseq` at the seam
absorbing the marshalling (the prologue's post PC/regs/mem entail the
load/store's pre — the `x13` kind-dword bridge and code-survival across the
memory-unchanged prologue). This validates that `seq`+`conseq` compose block
triples end-to-end.

NO Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (Eval_exprLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Logic.Triple

/-- Conjoin a **closed** proposition `K` (independent of the run configuration)
to both pre- and postcondition. Sound precisely because `K` mentions no state
the hidden run could touch — this is NOT the general (unsound) frame rule; it is
the degenerate case where the frame is a constant. Used to thread block-local
memory side-conditions (`LdOK`/`StOK` about the entry memory `m0`) across a
`seq` seam, where the underlying block preserves that memory. -/
theorem conj_const {P Q : Vsa.Machine.Config → Prop} {K : Prop}
    (h : Vsa.Logic.Triple P Q) :
    Vsa.Logic.Triple (fun c => P c ∧ K) (fun c => Q c ∧ K) := by
  intro c hc
  obtain ⟨c', hs, hq⟩ := h c hc.1
  exact ⟨c', hs, hq, hc.2⟩

end Vsa.Logic.Triple

namespace Vsa.Sim

/-! ## Block 1 — the neg PROLOGUE (`neg_prologue_block`, σ0→σ4)

Entry PC `0x800035ec`, exit PC `0x800039ac`. Loads the op token, `li a5,12`,
loads the kind dword, and takes `beq a4,a5`. Memory is unchanged; the frame is
carried in the post. `m0` threads the entry memory so a downstream seam can
recover the load/store side-conditions about it. -/

/-- Precondition of the neg prologue block, bundling `neg_prologue_block`'s
hypotheses over `Config = ⟨σ, tick, steps⟩`. -/
def negProloguePre (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x800035ec#64) ∧
  c.σ.regs.get? Register.minstret = some vm ∧
  c.σ.regs.get? Register.x8 = some v8 ∧
  c.σ.regs.get? Register.x2 = some v2 ∧
  c.σ.regs.get? Register.x9 = some v9 ∧
  c.σ.regs.get? Register.x1 = some v1 ∧
  Eval_exprLoaded c.σ.mem ∧
  bytesVal .lw [ob0,ob1,ob2,ob3] = (12#64 : BitVec 64) ∧
  LdOK4 c.σ.mem (v8 + sign_extend (m := 64) (0x008#12)) [ob0,ob1,ob2,ob3] ∧
  LdOK8 c.σ.mem (v2 + sign_extend (m := 64) (0x090#12)) [kb0,kb1,kb2,kb3,d4,d5,d6,d7] ∧
  c.tick < 2

/-- Postcondition of the neg prologue block: exit pins/tick/memory-survival +
the register frame (carried inside, per the Layer-1 design). -/
def negProloguePost (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x800039ac#64) ∧
  c.σ.regs.get? Register.x14 = some (bytesVal .lw [ob0,ob1,ob2,ob3]) ∧
  c.σ.regs.get? Register.x15 = some (12#64) ∧
  c.σ.regs.get? Register.x13 = some (bytesVal .ld [kb0,kb1,kb2,kb3,d4,d5,d6,d7]) ∧
  c.σ.regs.get? Register.x9 = some v9 ∧
  c.σ.regs.get? Register.x2 = some v2 ∧
  c.σ.regs.get? Register.x8 = some v8 ∧
  c.σ.regs.get? Register.x1 = some v1 ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.tick < 2 ∧
  (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
    (∀ n ∈ wrRegsM negPrologueBlk.body, (gprReg n == R) = false) →
    c.σ.regs.get? R = c.σ.regs.get? R)

theorem negPrologue_triple (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (negProloguePre vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 m0)
      (negProloguePost vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 m0) := by
  intro c hpre
  obtain ⟨hG, hm0, hpc, hmi, hx8, hx2, hx9, hx1, hmem, hob12, hLdO, hLdK, htick⟩ := hpre
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hx14', hx15', hx13',
      hx9', hx2', hx8', hx1', hmiw', hframe'⟩ :=
    neg_prologue_block c.σ c.tick c.steps vm v8 v2 v9 v1
      ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
      hG hpc hmi hx8 hx2 hx9 hx1 hmem hob12 hLdO hLdK htick
  refine ⟨⟨σ', i', c.steps + 4⟩, hsteps, hG', ?_, hpc', hx14', hx15', hx13',
    hx9', hx2', hx8', hx1', hmiw', hi', ?_⟩
  · rw [hmem', hm0]
  · intro R _ _; rfl

/-! ## Block 2 — the neg LOAD/STORE run (`neg_loadstore_full`, σ4→σ10)

Entry PC `0x800039ac`, exit PC `0x800039c4`. Three loads (payload/dead/kind) +
three error-arg staging stores. Memory ends in `writeLog` form; the frame rides
in the post. -/

/-- Precondition of the neg load/store block. -/
def negLoadStorePre (v2 v13 v9 v8 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8)
    (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (0x800039ac#64) ∧
  (∃ vm, c.σ.regs.get? Register.minstret = some vm) ∧
  c.σ.regs.get? Register.x2 = some v2 ∧
  c.σ.regs.get? Register.x13 = some v13 ∧
  c.σ.regs.get? Register.x9 = some v9 ∧
  c.σ.regs.get? Register.x8 = some v8 ∧
  Eval_exprLoaded c.σ.mem ∧
  LdOK8 c.σ.mem (v2 + sign_extend (m := 64) (0x098#12)) [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7] ∧
  LdOK8 c.σ.mem (v2 + sign_extend (m := 64) (0x0a0#12)) [q0,q1,q2,q3,q4,q5,q6,q7] ∧
  LdOK4 c.σ.mem (v2 + sign_extend (m := 64) (0x090#12)) [kb0,kb1,kb2,kb3] ∧
  StOK8 (v2 + sign_extend (m := 64) (0x0f0#12)) ∧
  StOK8 (v2 + sign_extend (m := 64) (0x0f8#12)) ∧
  StOK8 (v2 + sign_extend (m := 64) (0x100#12)) ∧
  c.tick < 2

/-- Postcondition of the neg load/store block: exit pins/tick + the memory in
`writeLog` form + the register frame (carried inside). -/
def negLoadStorePost (v2 v13 v9 v8 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.sailOutput = c.σ.sailOutput ∧
  c.σ.regs.get? Register.PC = some (0x800039c4#64) ∧
  c.σ.regs.get? Register.x11 = some (bytesVal .ld [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7]) ∧
  c.σ.regs.get? Register.x14 = some (bytesVal .ld [q0,q1,q2,q3,q4,q5,q6,q7]) ∧
  c.σ.regs.get? Register.x10 = some (bytesVal .lw [kb0,kb1,kb2,kb3]) ∧
  c.σ.regs.get? Register.x13 = some v13 ∧
  c.σ.regs.get? Register.x9 = some v9 ∧
  c.σ.regs.get? Register.x2 = some v2 ∧
  c.σ.regs.get? Register.x8 = some v8 ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.tick < 2 ∧
  c.σ.mem = writeLog m0 (wlogM negLoadStoreBlk.body [(2, v2), (13, v13), (9, v9)]
    [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]]) ∧
  (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
    (∀ n ∈ wrRegsM negLoadStoreBlk.body, (gprReg n == R) = false) →
    c.σ.regs.get? R = c.σ.regs.get? R)

theorem negLoadStore_triple (v2 v13 v9 v8 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (fun c => negLoadStorePre v2 v13 v9 v8
              pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 c ∧
              c.σ.mem = m0)
      (negLoadStorePost v2 v13 v9 v8
        pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 m0) := by
  intro c hpre
  obtain ⟨⟨hG, hpc, ⟨vm, hmi⟩, hx2, hx13, hx9, hx8, hmem,
      hLdP, hLdD, hLdK, hSt1, hSt2, hSt3, htick⟩, hm0⟩ := hpre
  obtain ⟨σ', i', hsteps, hi', hG', hout', hpc', hx11', hx14', hx10',
      hx13', hx9', hx2', hx8', hmiw', hmem', hframe'⟩ :=
    neg_loadstore_full c.σ c.tick c.steps vm v2 v13 v9 v8
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3
      hG hpc hmi hx2 hx13 hx9 hx8 hmem hLdP hLdD hLdK hSt1 hSt2 hSt3 htick
  refine ⟨⟨σ', i', c.steps + 6⟩, hsteps, hG', ?_, hpc', hx11', hx14', hx10',
    hx13', hx9', hx2', hx8', hmiw', hi', ?_, ?_⟩
  · rfl
  · rw [hmem', hm0]
  · intro R _ _; rfl

/-! ## Block 3 — the neg TAIL (`neg_tail_block`, σ10→σ15)

Entry PC `0x800039c4`, exit PC `0x800039d8`. `li a2,2; lw s0,4(s0); bne a0,a2
not-taken; neg a1,a1; mv a0,s1`. Memory unchanged; frame in the post. -/

/-- Precondition of the neg tail block. -/
def negTailPre (vm v8 v9 v2 p11 : BitVec 64) (lb0 lb1 lb2 lb3 : BitVec 8)
    (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (0x800039c4#64) ∧
  c.σ.regs.get? Register.minstret = some vm ∧
  c.σ.regs.get? Register.x8 = some v8 ∧
  c.σ.regs.get? Register.x10 = some (2#64) ∧
  c.σ.regs.get? Register.x9 = some v9 ∧
  c.σ.regs.get? Register.x11 = some p11 ∧
  c.σ.regs.get? Register.x2 = some v2 ∧
  Eval_exprLoaded c.σ.mem ∧
  LdOK4 c.σ.mem (v8 + sign_extend (m := 64) (0x004#12)) [lb0,lb1,lb2,lb3] ∧
  c.tick < 2

/-- Postcondition of the neg tail block: exit pins/tick/memory-survival + the
register frame (carried inside). -/
def negTailPost (vm v8 v9 v2 p11 : BitVec 64) (lb0 lb1 lb2 lb3 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x800039d8#64) ∧
  c.σ.regs.get? Register.x10 = some v9 ∧
  c.σ.regs.get? Register.x11 = some ((0#64) - p11) ∧
  c.σ.regs.get? Register.x9 = some v9 ∧
  c.σ.regs.get? Register.x2 = some v2 ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.tick < 2 ∧
  (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
    (∀ n ∈ wrChain negTailChain, (gprReg n == R) = false) →
    c.σ.regs.get? R = c.σ.regs.get? R)

theorem negTail_triple (vm v8 v9 v2 p11 : BitVec 64) (lb0 lb1 lb2 lb3 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (fun c => negTailPre vm v8 v9 v2 p11 lb0 lb1 lb2 lb3 c ∧ c.σ.mem = m0)
      (negTailPost vm v8 v9 v2 p11 lb0 lb1 lb2 lb3 m0) := by
  intro c hpre
  obtain ⟨⟨hG, hpc, hmi, hx8, hx10, hx9, hx11, hx2, hmem, hLdL, htick⟩, hm0⟩ := hpre
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hx10', hx11', hx9', hx2',
      hmiw', hframe'⟩ :=
    neg_tail_block c.σ c.tick c.steps vm v8 v9 v2 p11 lb0 lb1 lb2 lb3
      hG hpc hmi hx8 hx10 hx9 hx11 hx2 hmem hLdL htick
  refine ⟨⟨σ', i', c.steps + 5⟩, hsteps, hG', ?_, hpc', hx10', hx11', hx9', hx2',
    hmiw', hi', ?_⟩
  · rw [hmem', hm0]
  · intro R _ _; rfl

/-! ## Compose demo — `seq` + `conseq` chain two block triples

Chains the prologue triple to the load/store triple. The seam `conseq` marshals
the prologue's post into the load/store's pre:
* PC `0x800039ac` matches on the nose;
* the `x13` **kind-dword bridge** — prologue post fixes `x13 = bytesVal .ld
  [kb…]`, so the load/store's ghost `v13` is instantiated to that value;
* **code-survival** — prologue keeps `mem = m0`, so `Eval_exprLoaded` and the
  load/store side-conditions (`LdOK`/`StOK` on `m0`) carry across unchanged.

The composed precondition therefore additionally asserts, about the *entry*
memory `m0`, the load/store's memory side-conditions (they are ghost facts about
`m0` that the prologue does not itself supply, but which survive its
memory-preserving run). This is the sound assertion-carried framing the plan
calls for. -/

/-- The composed precondition: the prologue's own precondition, plus the
load/store's memory side-conditions asserted about the entry memory `m0`. -/
def negProLdStPre (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  negProloguePre vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 m0 c ∧
  Eval_exprLoaded m0 ∧
  LdOK8 m0 (v2 + sign_extend (m := 64) (0x098#12)) [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7] ∧
  LdOK8 m0 (v2 + sign_extend (m := 64) (0x0a0#12)) [q0,q1,q2,q3,q4,q5,q6,q7] ∧
  LdOK4 m0 (v2 + sign_extend (m := 64) (0x090#12)) [kb0,kb1,kb2,kb3] ∧
  StOK8 (v2 + sign_extend (m := 64) (0x0f0#12)) ∧
  StOK8 (v2 + sign_extend (m := 64) (0x0f8#12)) ∧
  StOK8 (v2 + sign_extend (m := 64) (0x100#12))

/-- **Compose demo (validates the abstraction).** The prologue and load/store
triples compose end-to-end via `Triple.seq`, the `conseq` at the seam absorbing
the marshalling. From `negProLdStPre` the machine runs `0x800035ec → 0x800039c4`
(σ0→σ10), landing the load/store block's post — the kind word `x10 = bytesVal
.lw [kb…]`, the payload `x11`, etc. -/
theorem neg_prologue_loadstore_triple (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (negProLdStPre vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
        pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 m0)
      (negLoadStorePost v2 (bytesVal .ld [kb0,kb1,kb2,kb3,d4,d5,d6,d7]) v9 v8
        pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 m0) := by
  -- `negProLdStPre = negProloguePre ∧ K` with `K` the *closed* m0-side-conditions.
  -- `conj_const` carries `K` across the prologue triple (sound: `K` names no run
  -- state); `seq` then chains the load/store triple; `conseq` at the seam marshals.
  refine Triple.seq
    (Triple.conj_const
      (negPrologue_triple vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 m0))
    (Triple.conseq
      (negLoadStore_triple v2 (bytesVal .ld [kb0,kb1,kb2,kb3,d4,d5,d6,d7]) v9 v8
        pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 m0)
      ?seam (fun c hc => hc))
  -- seam: `negProloguePost … ∧ (Eval_exprLoaded m0 ∧ LdOK/StOK about m0)`
  --       ⟹ `negLoadStorePre … ∧ mem = m0`.
  -- `x13` kind-dword bridge: prologue post fixes `x13 = bytesVal .ld [kb…]`,
  -- exactly the load/store ghost `v13`. Code-survival: `mem = m0` rewrites the
  -- `m0`-facts into the `c.σ.mem`-facts the load/store pre wants.
  intro c hc
  -- project by `.1`/`.2` so `GoodState` (itself a big ∧) is never split
  have hpost := hc.1
  have hmemL := hc.2.1
  have hLdP := hc.2.2.1
  have hLdD := hc.2.2.2.1
  have hLdK := hc.2.2.2.2.1
  have hSt1 := hc.2.2.2.2.2.1
  have hSt2 := hc.2.2.2.2.2.2.1
  have hSt3 := hc.2.2.2.2.2.2.2
  have hG := hpost.1
  have hm0 := hpost.2.1
  have hpc := hpost.2.2.1
  have hx13 := hpost.2.2.2.2.2.1
  have hx9 := hpost.2.2.2.2.2.2.1
  have hx2 := hpost.2.2.2.2.2.2.2.1
  have hx8 := hpost.2.2.2.2.2.2.2.2.1
  have hmiw := hpost.2.2.2.2.2.2.2.2.2.2.1
  have htick := hpost.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨hG, hpc, hmiw, hx2, hx13, hx9, hx8, ?_, ?_, ?_, ?_, hSt1, hSt2, hSt3, htick⟩, hm0⟩
  · rw [hm0]; exact hmemL
  · rw [hm0]; exact hLdP
  · rw [hm0]; exact hLdD
  · rw [hm0]; exact hLdK

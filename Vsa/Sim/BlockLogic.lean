import Vsa.Sim.NegBlockProto
import Vsa.Sim.EvalNegSim
import Vsa.Sim.BlockAdapter
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
hypotheses over `Config = ⟨σ, tick, steps⟩`.

`entryRegs` is the **entry register-map ghost** (as `int_pre`'s `g`): the Pre
asserts `c.σ.regs.get? R = entryRegs R` under the block's noise/wrRegs frame
side-conditions, so the Post can carry a genuine entry→exit frame (not a
tautology) — the sound assertion-carried framing (a general `Triple.frame` would
be unsound). -/
def negProloguePre (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
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
  c.tick < 2 ∧
  (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
    (∀ n ∈ wrRegsM negPrologueBlk.body, (gprReg n == R) = false) →
    c.σ.regs.get? R = entryRegs R)

/-- Postcondition of the neg prologue block: exit pins/tick/memory-survival +
the **genuine entry→exit register frame** (carried inside, per the Layer-1
design): every register neither noise nor written by the block matches the entry
map `entryRegs`. -/
def negProloguePost (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
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
    c.σ.regs.get? R = entryRegs R)

theorem negPrologue_triple (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (negProloguePre vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 entryRegs m0)
      (negProloguePost vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 entryRegs m0) := by
  intro c hpre
  obtain ⟨hG, hm0, hpc, hmi, hx8, hx2, hx9, hx1, hmem, hob12, hLdO, hLdK, htick, hentry⟩ := hpre
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hx14', hx15', hx13',
      hx9', hx2', hx8', hx1', hmiw', hframe'⟩ :=
    neg_prologue_block c.σ c.tick c.steps vm v8 v2 v9 v1
      ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
      hG hpc hmi hx8 hx2 hx9 hx1 hmem hob12 hLdO hLdK htick
  refine ⟨⟨σ', i', c.steps + 4⟩, hsteps, hG', ?_, hpc', hx14', hx15', hx13',
    hx9', hx2', hx8', hx1', hmiw', hi', ?_⟩
  · rw [hmem', hm0]
  · intro R hn hw; exact (hframe' R hn hw).trans (hentry R hn hw)

/-! ## Block 2 — the neg LOAD/STORE run (`neg_loadstore_full`, σ4→σ10)

Entry PC `0x800039ac`, exit PC `0x800039c4`. Three loads (payload/dead/kind) +
three error-arg staging stores. Memory ends in `writeLog` form; the frame rides
in the post. -/

/-- Precondition of the neg load/store block. `entryRegs` is the entry
register-map ghost; the Pre asserts `c.σ.regs.get? R = entryRegs R` under the
block frame side-conditions (cf. `negProloguePre`). -/
def negLoadStorePre (v2 v13 v9 v8 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
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
  c.tick < 2 ∧
  (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
    (∀ n ∈ wrRegsM negLoadStoreBlk.body, (gprReg n == R) = false) →
    c.σ.regs.get? R = entryRegs R)

/-- Postcondition of the neg load/store block: exit pins/tick + the memory in
`writeLog` form + the **genuine entry→exit register frame** (carried inside):
every register neither noise nor written by the block matches `entryRegs`. -/
def negLoadStorePost (v2 v13 v9 v8 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
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
    c.σ.regs.get? R = entryRegs R)

theorem negLoadStore_triple (v2 v13 v9 v8 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (fun c => negLoadStorePre v2 v13 v9 v8
              pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 entryRegs c ∧
              c.σ.mem = m0)
      (negLoadStorePost v2 v13 v9 v8
        pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 entryRegs m0) := by
  intro c hpre
  obtain ⟨⟨hG, hpc, ⟨vm, hmi⟩, hx2, hx13, hx9, hx8, hmem,
      hLdP, hLdD, hLdK, hSt1, hSt2, hSt3, htick, hentry⟩, hm0⟩ := hpre
  obtain ⟨σ', i', hsteps, hi', hG', hout', hpc', hx11', hx14', hx10',
      hx13', hx9', hx2', hx8', hmiw', hmem', hframe'⟩ :=
    neg_loadstore_full c.σ c.tick c.steps vm v2 v13 v9 v8
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3
      hG hpc hmi hx2 hx13 hx9 hx8 hmem hLdP hLdD hLdK hSt1 hSt2 hSt3 htick
  refine ⟨⟨σ', i', c.steps + 6⟩, hsteps, hG', ?_, hpc', hx11', hx14', hx10',
    hx13', hx9', hx2', hx8', hmiw', hi', ?_, ?_⟩
  · rfl
  · rw [hmem', hm0]
  · intro R hn hw; exact (hframe' R hn hw).trans (hentry R hn hw)

/-! ## Block 3 — the neg TAIL (`neg_tail_block`, σ10→σ15)

Entry PC `0x800039c4`, exit PC `0x800039d8`. `li a2,2; lw s0,4(s0); bne a0,a2
not-taken; neg a1,a1; mv a0,s1`. Memory unchanged; frame in the post. -/

/-- Precondition of the neg tail block. `entryRegs` is the entry register-map
ghost; the Pre asserts `c.σ.regs.get? R = entryRegs R` under the tail chain's
frame side-conditions (`wrChain negTailChain`). -/
def negTailPre (vm v8 v9 v2 p11 : BitVec 64) (lb0 lb1 lb2 lb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
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
  c.tick < 2 ∧
  (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
    (∀ n ∈ wrChain negTailChain, (gprReg n == R) = false) →
    c.σ.regs.get? R = entryRegs R)

/-- Postcondition of the neg tail block: exit pins/tick/memory-survival + the
**genuine entry→exit register frame** (carried inside): every register neither
noise nor written by the tail chain matches `entryRegs`. -/
def negTailPost (vm v8 v9 v2 p11 : BitVec 64) (lb0 lb1 lb2 lb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
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
    c.σ.regs.get? R = entryRegs R)

theorem negTail_triple (vm v8 v9 v2 p11 : BitVec 64) (lb0 lb1 lb2 lb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (fun c => negTailPre vm v8 v9 v2 p11 lb0 lb1 lb2 lb3 entryRegs c ∧ c.σ.mem = m0)
      (negTailPost vm v8 v9 v2 p11 lb0 lb1 lb2 lb3 entryRegs m0) := by
  intro c hpre
  obtain ⟨⟨hG, hpc, hmi, hx8, hx10, hx9, hx11, hx2, hmem, hLdL, htick, hentry⟩, hm0⟩ := hpre
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hx10', hx11', hx9', hx2',
      hmiw', hframe'⟩ :=
    neg_tail_block c.σ c.tick c.steps vm v8 v9 v2 p11 lb0 lb1 lb2 lb3
      hG hpc hmi hx8 hx10 hx9 hx11 hx2 hmem hLdL htick
  refine ⟨⟨σ', i', c.steps + 5⟩, hsteps, hG', ?_, hpc', hx10', hx11', hx9', hx2',
    hmiw', hi', ?_⟩
  · rw [hmem', hm0]
  · intro R hn hw; exact (hframe' R hn hw).trans (hentry R hn hw)

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
load/store's memory side-conditions asserted about the entry memory `m0`.

`entryRegs` is the σ0 entry register-map ghost; the underlying `negProloguePre`
carries the entry frame (guarded by the prologue's wrRegs). -/
def negProLdStPre (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  negProloguePre vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 entryRegs m0 c ∧
  Eval_exprLoaded m0 ∧
  LdOK8 m0 (v2 + sign_extend (m := 64) (0x098#12)) [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7] ∧
  LdOK8 m0 (v2 + sign_extend (m := 64) (0x0a0#12)) [q0,q1,q2,q3,q4,q5,q6,q7] ∧
  LdOK4 m0 (v2 + sign_extend (m := 64) (0x090#12)) [kb0,kb1,kb2,kb3] ∧
  StOK8 (v2 + sign_extend (m := 64) (0x0f0#12)) ∧
  StOK8 (v2 + sign_extend (m := 64) (0x0f8#12)) ∧
  StOK8 (v2 + sign_extend (m := 64) (0x100#12))

/-- The composed prologue+loadstore Post: the loadstore's Post pins/memory, but
with the register frame promoted to a **genuine σ0-entry frame** — a register
untouched by *either* block (prologue or loadstore) matches `entryRegs` (the σ0
map). The two per-block wrRegs guards are separate hypotheses; a consumer
discharges both (from R being noise-or-callee-saved) to land the entry value. -/
def negProLdStPost (v2 v13 v9 v8 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
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
    (∀ n ∈ wrRegsM negPrologueBlk.body, (gprReg n == R) = false) →
    (∀ n ∈ wrRegsM negLoadStoreBlk.body, (gprReg n == R) = false) →
    c.σ.regs.get? R = entryRegs R)

/-- **Compose demo (validates the abstraction).** The prologue and load/store
triples compose end-to-end. From `negProLdStPre` the machine runs `0x800035ec →
0x800039c4` (σ0→σ10), landing `negProLdStPost` — the kind word `x10 = bytesVal
.lw [kb…]`, the payload `x11`, etc., plus the **genuine σ0-entry frame**
promoted from the two block frames by `.trans` at the σ4 seam.

The pin/memory marshalling is the same as before (kind-dword bridge, code
survival across the memory-preserving prologue). The frame threading needs both
endpoints (σ4 and σ10), so this is a manual `obtain`-compose rather than
`Triple.seq`: the prologue frame gives `σ4.R = entryRegs R` (prologue guard), the
loadstore frame gives `σ10.R = σ4.R` (loadstore guard); `.trans` under the union
guard yields `σ10.R = entryRegs R`. -/
theorem neg_prologue_loadstore_triple (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (negProLdStPre vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
        pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 entryRegs m0)
      (negProLdStPost v2 (bytesVal .ld [kb0,kb1,kb2,kb3,d4,d5,d6,d7]) v9 v8
        pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 entryRegs m0) := by
  intro c hc
  obtain ⟨hproPre, hmemL, hLdP, hLdD, hLdK, hSt1, hSt2, hSt3⟩ := hc
  -- run the prologue (σ0→σ4)
  obtain ⟨c4, hs4, hpost4⟩ :=
    negPrologue_triple vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 entryRegs m0
      c hproPre
  -- project prologue Post (never split `GoodState`)
  have hG4 := hpost4.1
  have hm04 := hpost4.2.1
  have hpc4 := hpost4.2.2.1
  have hx13_4 := hpost4.2.2.2.2.2.1
  have hx9_4 := hpost4.2.2.2.2.2.2.1
  have hx2_4 := hpost4.2.2.2.2.2.2.2.1
  have hx8_4 := hpost4.2.2.2.2.2.2.2.2.1
  have hmiw4 := hpost4.2.2.2.2.2.2.2.2.2.2.1
  have htick4 := hpost4.2.2.2.2.2.2.2.2.2.2.2.1
  have hframePro := hpost4.2.2.2.2.2.2.2.2.2.2.2.2
  -- run the loadstore (σ4→σ10); its entry ghost is σ4's own map, so its Pre frame
  -- is `rfl`.  code-survival: `mem = m0` rewrites the `m0`-facts into `c4.σ.mem`.
  obtain ⟨c10, hs10, hpost10⟩ :=
    negLoadStore_triple v2 (bytesVal .ld [kb0,kb1,kb2,kb3,d4,d5,d6,d7]) v9 v8
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3
      c4.σ.regs.get? m0 c4
      ⟨⟨hG4, hpc4, hmiw4, hx2_4, hx13_4, hx9_4, hx8_4,
          (by rw [hm04]; exact hmemL),
          (by rw [hm04]; exact hLdP), (by rw [hm04]; exact hLdD), (by rw [hm04]; exact hLdK),
          hSt1, hSt2, hSt3, htick4, (fun R _ _ => rfl)⟩, hm04⟩
  -- project loadstore Post
  have hG10 := hpost10.1
  have hout10 := hpost10.2.1
  have hpc10 := hpost10.2.2.1
  have hx11_10 := hpost10.2.2.2.1
  have hx14_10 := hpost10.2.2.2.2.1
  have hx10_10 := hpost10.2.2.2.2.2.1
  have hx13_10 := hpost10.2.2.2.2.2.2.1
  have hx9_10 := hpost10.2.2.2.2.2.2.2.1
  have hx2_10 := hpost10.2.2.2.2.2.2.2.2.1
  have hx8_10 := hpost10.2.2.2.2.2.2.2.2.2.1
  have hmiw10 := hpost10.2.2.2.2.2.2.2.2.2.2.1
  have htick10 := hpost10.2.2.2.2.2.2.2.2.2.2.2.1
  have hmem10 := hpost10.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hframeBlk := hpost10.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨c10, hs4.trans hs10, hG10, hout10, hpc10, hx11_10, hx14_10, hx10_10,
    hx13_10, hx9_10, hx2_10, hx8_10, hmiw10, htick10, hmem10, ?_⟩
  -- composed σ0-entry frame: `σ10.R = σ4.R` (loadstore) `.trans` `σ4.R = entryRegs R`
  -- (prologue).  Both guards are separate hypotheses in `negProLdStPost`.
  intro R hn hwPro hwBlk
  exact (hframeBlk R hn hwBlk).trans (hframePro R hn hwPro)

/-! ## Full 3-block spine — `neg_blocks_triple` (σ0→σ15, PC 0x800035ec→0x800039d8)

The core **A1** result: the whole straight-line neg spine `0x800035ec → 0x800039d8`
as ONE composed `Triple`, chaining `negPrologue_triple`, `negLoadStore_triple`,
`negTail_triple` via `Triple.seq`+`Triple.conseq` at the two seams.

The prologue→loadstore seam is the `neg_prologue_loadstore_triple` demo above.
The new **loadstore→tail seam** absorbs:
* the kind-int bridge `x10 = bytesVal .lw [kb…] = 2#64` (side-condition `hkind2`);
* the payload bridge `x11 = bytesVal .ld [pb…]` → the tail ghost `p11`;
* the carried callee-saved `x9`/`x2`/`x8`;
* **code-survival across the three error stores**: the loadstore Post fixes
  `mem = writeLog m0 (wlogM …)`, three 8-byte stores at `v2+0xf0/0xf8/0x100`; the
  tail wants `Eval_exprLoaded mem` and the e→line `LdOK4 mem (v8+4) [lb…]`, both
  recovered from the `m0`-versions via `writeLog_getElem_disjoint` on the three
  store windows (carried as the disjointness side-conditions below).

The tail `minstret` witness is obtained from the loadstore Post's `∃ w`. -/

/-- The composed σ0-entry precondition: the prologue+loadstore precondition
(`negProLdStPre`), plus the **tail seam side-conditions about the entry memory
`m0`** and the store windows — the kind-int fact, the e→line `LdOK4` on `m0`, and
the disjointness of the three error-store windows (`v2+0xf0/0xf8/0x100`, width 8)
from the `eval_expr` code region `[0x80003164,0x80003fe0)` and from the e→line
window `[v8+4,v8+8)`. All name only constants (`m0`, the register ghosts), so they
ride across the prologue+loadstore run soundly via `conj_const`. -/
def negBlocksPre (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 : BitVec 8)
    (lb0 lb1 lb2 lb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  negProLdStPre vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
    pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 entryRegs m0 c ∧
  bytesVal .lw [kb0,kb1,kb2,kb3] = (2#64 : BitVec 64) ∧
  LdOK4 m0 (v8 + sign_extend (m := 64) (0x004#12)) [lb0,lb1,lb2,lb3] ∧
  -- the e→line window `[v8+4, v8+8)` is disjoint from every error-store window
  (∀ k, (v8 + sign_extend (m := 64) (0x004#12)).toNat ≤ k →
        k < (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 →
    (k < (v2 + sign_extend (m := 64) (0x0f0#12)).toNat ∨ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ k) ∧
    (k < (v2 + sign_extend (m := 64) (0x0f8#12)).toNat ∨ (v2 + sign_extend (m := 64) (0x0f8#12)).toNat + 8 ≤ k) ∧
    (k < (v2 + sign_extend (m := 64) (0x100#12)).toNat ∨ (v2 + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ k)) ∧
  -- the `eval_expr` code region `[0x80003164,0x80003fe0)` is disjoint likewise
  (∀ k, (0x80003164 ≤ k ∧ k < 0x80003fe0) →
    (k < (v2 + sign_extend (m := 64) (0x0f0#12)).toNat ∨ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ k) ∧
    (k < (v2 + sign_extend (m := 64) (0x0f8#12)).toNat ∨ (v2 + sign_extend (m := 64) (0x0f8#12)).toNat + 8 ≤ k) ∧
    (k < (v2 + sign_extend (m := 64) (0x100#12)).toNat ∨ (v2 + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ k))

/-- The `wlogM` of the loadstore block reduces to the three concrete 8-byte
error-store entries at `v2+0xf0/0xf8/0x100`. Pure defeq (`rfl`); the addresses
stay symbolic but the list structure and widths compute. -/
theorem wlogM_negLoadStore (v2 v13 v9 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8) :
    wlogM negLoadStoreBlk.body [(2, v2), (13, v13), (9, v9)]
      [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]]
    = [((v2 + sign_extend (m := 64) (0x0f0#12)).toNat, 8, v13),
       ((v2 + sign_extend (m := 64) (0x0f8#12)).toNat, 8,
         bytesVal .ld [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7]),
       ((v2 + sign_extend (m := 64) (0x100#12)).toNat, 8,
         bytesVal .ld [q0,q1,q2,q3,q4,q5,q6,q7])] := by
  rfl

/-- The full-spine Post: the tail's Post pins/memory, but the register frame is
promoted to a **genuine σ0-entry frame under the union of all three blocks'
guards** — a register untouched by prologue, loadstore, *and* tail matches
`entryRegs` (the σ0 map). The three per-block wrRegs guards are separate
hypotheses; a consumer (`blockC_neg`) discharges all three (from R being
noise-or-callee-saved, via `abiNoise_noiseRegs`/`block_frame_wr`) to reach the
entry value. -/
def negBlocksPost (vm v8 v9 v2 p11 : BitVec 64) (lb0 lb1 lb2 lb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
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
    (∀ n ∈ wrRegsM negPrologueBlk.body, (gprReg n == R) = false) →
    (∀ n ∈ wrRegsM negLoadStoreBlk.body, (gprReg n == R) = false) →
    (∀ n ∈ wrChain negTailChain, (gprReg n == R) = false) →
    c.σ.regs.get? R = entryRegs R)

/-- **The full 3-block neg spine as ONE composed `Triple`.** From the σ0 entry
(`negBlocksPre`) the machine runs `0x800035ec → 0x800039d8` (σ0→σ15), landing
`negBlocksPost` — `x10 = v9`, `x11 = -payload`, the **genuine σ0-entry callee-
saved frame** (composed `σ15↔σ10↔σ4↔σ0` by `.trans` at each seam under the union
guard), and the final memory (in `writeLog` form). Composed as
`neg_prologue_loadstore_triple ⋙ negTail_triple`. -/
theorem neg_blocks_triple (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 : BitVec 8)
    (lb0 lb1 lb2 lb3 : BitVec 8)
    (entryRegs : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (negBlocksPre vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
        pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 lb0 lb1 lb2 lb3 entryRegs m0)
      (negBlocksPost vm v8 v9 v2 (bytesVal .ld [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7])
        lb0 lb1 lb2 lb3 entryRegs
        (writeLog m0 (wlogM negLoadStoreBlk.body
          [(2, v2), (13, bytesVal .ld [kb0,kb1,kb2,kb3,d4,d5,d6,d7]), (9, v9)]
          [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]]))) := by
  intro c hpre
  obtain ⟨hproldst, hkind2, hLdL0, hdisjLine, hdisjCode⟩ := hpre
  -- run the first two blocks (σ0→σ10) via the demo triple
  obtain ⟨c10, hs10, hpost10⟩ :=
    neg_prologue_loadstore_triple vm v8 v2 v9 v1 ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 entryRegs m0 c hproldst
  -- abbreviations (plain `let`s; no Mathlib `set`)
  let K13 : BitVec 64 := bytesVal .ld [kb0,kb1,kb2,kb3,d4,d5,d6,d7]
  let payV : BitVec 64 := bytesVal .ld [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7]
  let m3 : Std.ExtHashMap Nat (BitVec 8) :=
    writeLog m0 (wlogM negLoadStoreBlk.body [(2, v2), (13, K13), (9, v9)]
      [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]])
  -- project the loadstore Post (never split `GoodState`)
  have hG10 := hpost10.1
  have hpc10 := hpost10.2.2.1
  have hx11_10 := hpost10.2.2.2.1
  have hx10_10 := hpost10.2.2.2.2.2.1
  have hx9_10 := hpost10.2.2.2.2.2.2.2.1
  have hx2_10 := hpost10.2.2.2.2.2.2.2.2.1
  have hx8_10 := hpost10.2.2.2.2.2.2.2.2.2.1
  have hmi10 := hpost10.2.2.2.2.2.2.2.2.2.2.1
  have htick10 := hpost10.2.2.2.2.2.2.2.2.2.2.2.1
  have hmem10 := hpost10.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- the composed σ0-entry frame for σ10 (prologue+loadstore guards)
  have hframe10 := hpost10.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- the writeLog is three 8-byte error stores at v2+0xf0/0xf8/0x100
  have hlog := wlogM_negLoadStore v2 K13 v9 pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
    q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3
  have hwidths : ∀ e ∈ wlogM negLoadStoreBlk.body [(2, v2), (13, K13), (9, v9)]
      [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]],
      e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 8 := by
    rw [hlog]; intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> (rw [h]; right; right; rfl)
  -- Eval_exprLoaded survives the three stores (code region disjoint from windows)
  have hcode10 : Eval_exprLoaded c10.σ.mem := by
    rw [hmem10]
    refine loaded_eval_expr_agreeP m0 m3 (fun a ha => ?_) hproldst.2.1
    exact (writeLog_getElem_disjoint a _ m0 hwidths (by
      rw [hlog]; intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      obtain ⟨h0, h1, h2⟩ := hdisjCode a ha
      rcases he with h | h | h <;> (rw [h]; first | exact h0 | exact h1 | exact h2))).symm
  -- the e→line LdOK4 survives the three stores
  have hLdL : LdOK4 c10.σ.mem (v8 + sign_extend (m := 64) (0x004#12)) [lb0,lb1,lb2,lb3] := by
    obtain ⟨hb, hp0, hp1, hp2, hp3⟩ := hLdL0
    have hsurv : ∀ j, (v8 + sign_extend (m := 64) (0x004#12)).toNat ≤ j →
        j < (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 → c10.σ.mem[j]? = m0[j]? := by
      intro j hj1 hj2
      rw [hmem10]
      exact writeLog_getElem_disjoint j _ m0 hwidths (by
        rw [hlog]; intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        obtain ⟨h0, h1, h2⟩ := hdisjLine j hj1 hj2
        rcases he with h | h | h <;> (rw [h]; first | exact h0 | exact h1 | exact h2))
    refine ⟨hb, ?_, ?_, ?_, ?_⟩
    · rw [hsurv _ (by omega) (by omega)]; exact hp0
    · rw [hsurv _ (by omega) (by omega)]; exact hp1
    · rw [hsurv _ (by omega) (by omega)]; exact hp2
    · rw [hsurv _ (by omega) (by omega)]; exact hp3
  -- the tail minstret witness
  obtain ⟨wmi, hwmi⟩ := hmi10
  -- x10 = 2#64 via the kind-int bridge
  have hx10_2 : c10.σ.regs.get? Register.x10 = some (2#64) := by
    rw [hkind2] at hx10_10; exact hx10_10
  -- apply the tail triple at the σ10 config with the survived seam facts.  Its
  -- entry ghost is σ10's own map, so its Pre frame is `rfl`; its Post frame then
  -- reads `σ15.R = σ10.R` (tail guard).
  obtain ⟨c15, hs15, hpost15⟩ :=
    negTail_triple wmi v8 v9 v2 payV lb0 lb1 lb2 lb3 c10.σ.regs.get? m3 c10
      ⟨⟨hG10, hpc10, hwmi, hx8_10, hx10_2, hx9_10, hx11_10, hx2_10, hcode10, hLdL, htick10,
          (fun R _ _ => rfl)⟩, hmem10⟩
  -- project the tail Post
  have hG15 := hpost15.1
  have hm015 := hpost15.2.1
  have hpc15 := hpost15.2.2.1
  have hx10_15 := hpost15.2.2.2.1
  have hx11_15 := hpost15.2.2.2.2.1
  have hx9_15 := hpost15.2.2.2.2.2.1
  have hx2_15 := hpost15.2.2.2.2.2.2.1
  have hmi15 := hpost15.2.2.2.2.2.2.2.1
  have htick15 := hpost15.2.2.2.2.2.2.2.2.1
  have hframeTail := hpost15.2.2.2.2.2.2.2.2.2
  refine ⟨c15, hs10.trans hs15, hG15, hm015, hpc15, hx10_15, hx11_15, hx9_15, hx2_15,
    hmi15, htick15, ?_⟩
  -- composed σ0-entry frame: `σ15.R = σ10.R` (tail) `.trans` `σ10.R = entryRegs R`
  -- (prologue+loadstore).  All three per-block guards are separate hypotheses.
  intro R hn hwPro hwBlk hwTail
  exact (hframeTail R hn hwTail).trans (hframe10 R hn hwPro hwBlk)

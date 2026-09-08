import Vsa.Sim.EvalRecCommon
import Vsa.Sim.CoherentReturn

open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Machine Vsa.Logic
open Vsa.Alloc

namespace Vsa.Sim

/-- Selected representation maps at the child endpoint, independent of the
call's register ghosts. The child simulation supplies every field together. -/
structure EvalReturnData (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Addr → Nat) (nf nc : Nat) (st : Vsa.While.St) (v : Value) (a : Nat)
    (Owned : (Addr → Nat) → (Addr → Nat) → Mem → Prop) (c : Config) : Prop where
  selected : ∃ resultF resultC, ReturnRepr N A phiF phiC resultF resultC nf nc
    st.store [(a, v)] Owned (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem

/-- The recursive exit retains one map pair for its result, store, and ownership.
The existential is inside the reached configuration's postcondition. -/
structure EvalReturn
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Addr → Nat) (nf nc : Nat) (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (m0 : Mem)
    (Owned : (Addr → Nat) → (Addr → Nat) → Mem → Prop) (c : Config) : Prop where
  exit : EvalExitD g N A SL phiF phiC nf nc st v sp r sret m0 c
  repr : EvalReturnData N A SL phiF phiC nf nc st v sret.toNat Owned c

/-- Select the producer's common maps in every map-dependent exit field.
The machine endpoint, presence, and complete result words come from the exit. -/
theorem EvalExitD.withReturnRepr
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {oldF oldC phiF phiC resultF resultC : Addr → Nat} {oldNf oldNc nf nc : Nat}
    {st : Vsa.While.St} {v : Value} {sp r sret : BitVec 64} {m0 : Mem} {c : Config}
    {Owned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    (h : EvalExitD g N A SL oldF oldC oldNf oldNc st v sp r sret m0 c)
    (hr : ReturnRepr N A phiF phiC resultF resultC nf nc st.store [(sret.toNat, v)]
      Owned (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem) :
    EvalReturn g N A SL phiF phiC nf nc st v sp r sret m0 Owned c := by
  obtain ⟨hExit, hPresence, hWords, _store⟩ := h
  have hExit' : EvalExit g N A SL phiF phiC nf nc st v sp r sret m0 c :=
    { hExit with
      result := ⟨resultC, hr.closures, hr.values _ _ (List.mem_singleton_self _)⟩
      store := ⟨resultF, resultC, hr.frames, hr.closures, hr.storeRepr⟩ }
  exact ⟨⟨hExit', hPresence, hWords, resultF, resultC, hr.frames, hr.closures, hr.survives⟩,
    ⟨resultF, resultC, hr⟩⟩

/-- Return through the shared epilogue at the producer's chosen maps.
The prefix witnesses cover the caller's old objects; fresh objects retain the
producer's exact representation. Ownership is preserved at the same endpoint. -/
theorem blockD_v_return
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC resultF resultC : Addr → Nat) (nf nc : Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    (Owned : (Addr → Nat) → (Addr → Nat) → Mem → Prop)
    (hf : PhiExtends phiF resultF nf) (hc : PhiExtends phiC resultC nc) :
    Triple
      (PreEpilogueOwned g N A SL resultF resultC st v sp r sret v8 v9 v18 out0 m0 Owned)
      (EvalReturn g N A SL phiF phiC nf nc st v sp r sret m0 Owned) := by
  apply (blockD_v_rec_coherent g N A SL resultF resultC st v
    sp r sret v8 v9 v18 out0 m0 Owned).conseq (fun _ h => h)
  intro c h
  exact h.result.withReturnRepr
    { h.extra with frames := hf, closures := hc }

/-- Legacy exits can recover a common map for references in the entry prefix.
Fresh closures require the producer to supply `EvalReturn.repr` directly. -/
theorem EvalExitD.coherent_of_bounded
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Addr → Nat} {nf nc : Nat} {st : Vsa.While.St} {v : Value}
    {sp r sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : EvalExitD g N A SL phiF phiC nf nc st v sp r sret m0 c)
    (hb : ValueClosuresBounded nc v) :
    EvalReturn g N A SL phiF phiC nf nc st v sp r sret m0 (fun _ _ _ => True) c := by
  refine ⟨h, ⟨?_⟩⟩
  obtain ⟨he, _, _, resultF, resultC, hf, hc, hs⟩ := h
  obtain ⟨valueC, hvc, hv⟩ := he.result
  refine ⟨resultF, resultC, hf, hc, ?_, True.intro, hs⟩
  intro a w haw
  have haw' : (a, w) = (sret.toNat, v) := List.mem_singleton.mp haw
  cases haw'
  exact valueRepr_phic_mono hb (fun k hk => (hc k hk).trans (hvc k hk).symm) hv

/-- Recursive induction contract with ownership indexed by the actual maps.
Ownership suppliers may depend on the chosen native addresses and arena. -/
structure EvalReturnIH
    (Owned : NativeAddrs → Arena → (Addr → Nat) → (Addr → Nat) → Mem → Prop)
    (st : Vsa.While.St) (d env : Nat) (e : Expr) (st' : Vsa.While.St) (v : Value) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple (EvalEntry g N A SL phiF phiC st d env e sp r sret aEnv aExpr m0)
      (EvalReturn g N A SL phiF phiC st.store.frames.size st.store.closures.size
        st' v sp r sret m0 (Owned N A))

/-- Feed the existing child-call execution while retaining its selected maps
and ownership. The ordinary exit and extra facts share the same endpoint. -/
theorem EvalReturnIH.withMaps
    {Owned : NativeAddrs → Arena → (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalReturnIH Owned st d env e st' v) :
    EvalIHWith (fun N A SL phiF phiC a =>
      EvalReturnData N A SL phiF phiC st.store.frames.size st.store.closures.size
        st' v a (Owned N A)) st d env e st' v where
  run := fun g N A SL phiF phiC sp r sret aEnv aExpr m0 =>
    (h.run g N A SL phiF phiC sp r sret aEnv aExpr m0).conseq
      (fun _ hp => hp) (fun _ hp => ⟨hp.exit, hp.repr⟩)

theorem EvalReturnIH.forget
    {Owned : NativeAddrs → Arena → (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalReturnIH Owned st d env e st' v) : EvalIH st d env e st' v := by
  intro g N A SL phiF phiC sp r sret aEnv aExpr m0
  exact (h.run g N A SL phiF phiC sp r sret aEnv aExpr m0).conseq
    (fun _ hp => hp) (fun _ hp => hp.exit)

/-- One supplier covers every legacy child whose returned references predate it. -/
theorem EvalIH.coherent_of_bounded
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalIH st d env e st' v) (hb : ValueClosuresBounded st.store.closures.size v) :
    EvalReturnIH (fun _ _ _ _ _ => True) st d env e st' v where
  run := fun g N A SL phiF phiC sp r sret aEnv aExpr m0 =>
    (h g N A SL phiF phiC sp r sret aEnv aExpr m0).conseq
      (fun _ hp => hp) (fun _ hp => hp.coherent_of_bounded hb)

/-- The weakest ownership index: every landed coherent supplier is stated at it,
and it is the index of the recursor motive `TermSimAssembly.mEvalE`. -/
abbrev TrivialOwned : NativeAddrs → Arena → (Addr → Nat) → (Addr → Nat) → Mem → Prop :=
  fun _ _ _ _ _ => True

/-- Binary-operator results are integers, booleans, or strings: no closure reference. -/
theorem binOpSem_closuresBounded {s : Store} {op : BinOp} {l r v : Value} {n : Nat}
    (h : binOpSem s op l r = some v) : ValueClosuresBounded n v := by
  cases op <;> cases l <;> cases r <;>
    simp only [binOpSem, Option.some.injEq, reduceCtorEq] at h <;>
    (try split at h) <;> (try cases h) <;> (try subst h) <;> trivial

/-- The facts a producer holds at the shared epilogue entry `mpre`, at the ONE
map pair its result and store are represented with: presence, the complete
result words, and store survival across the stack region. Every arm that runs
`blockD_v_return` supplies this record from its actual construction. -/
structure EpilogueEntryFacts (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Addr → Nat) (st : Vsa.While.St) (sret : BitVec 64)
    (m0 mpre : Mem) : Prop where
  presence : MemExtends m0 mpre
  words : ValueWordsTotal mpre sret.toNat
  survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mpre[k]? = m'[k]?) →
    StoreRepr m' N A phiF phiC st.store

/-- The epilogue-entry state with its facts is the owned pre-epilogue state at
the trivial ownership. -/
theorem EpilogueEntryFacts.preEpilogueOwned
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {v : Value} {sp r sret v8 v9 v18 : BitVec 64}
    {out0 : Array String} {m0 mpre : Mem} {c : Config}
    (hPre : PreEpilogueV g N A SL phiF phiC st v sp r sret v8 v9 v18 out0 m0 mpre c)
    (hF : EpilogueEntryFacts N A SL phiF phiC st sret m0 mpre) :
    PreEpilogueOwned g N A SL phiF phiC st v sp r sret v8 v9 v18 out0 m0
      (fun _ _ _ => True) c :=
  ⟨mpre, ⟨hPre, hF.presence, hF.words, hF.survives⟩, trivial⟩

/-- Land the coherent return from an arm's epilogue entry at the maps it selected
(`resultF`/`resultC`, extending the entry maps over the entry objects). This is
the whole epilogue of every allocating arm: `fn` (closures grown by one) and
`call` (frames and closures grown by the body). -/
theorem armReturn_of_facts
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC resultF resultC : Addr → Nat) (nf nc : Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    (hf : PhiExtends phiF resultF nf) (hc : PhiExtends phiC resultC nc) :
    Triple
      (fun c => ∃ mpre,
        PreEpilogueV g N A SL resultF resultC st v sp r sret v8 v9 v18 out0 m0 mpre c ∧
        EpilogueEntryFacts N A SL resultF resultC st sret m0 mpre)
      (EvalReturn g N A SL phiF phiC nf nc st v sp r sret m0 (fun _ _ _ => True)) :=
  (blockD_v_return g N A SL phiF phiC resultF resultC nf nc st v sp r sret v8 v9 v18
    out0 m0 (fun _ _ _ => True) hf hc).conseq
    (fun _ h => let ⟨_, hPre, hF⟩ := h; hF.preEpilogueOwned hPre)
    (fun _ h => h)

/-- Identity-map exit widening: presence plus store survival at the ENTRY maps.
The leaf whose result is represented at the entry closures map (the variable
lookup copies a frame slot) needs exactly this, not the map-existential
`Widen`. -/
structure ReturnWiden (ExitP : Config → Prop)
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (m0 : Mem) : Prop where
  pres : ∀ c : Config, ExitP c → MemExtends m0 c.σ.mem
  surv : ∀ c : Config, ExitP c → ∀ m' : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A phiF phiC st.store

/-- A leaf exit whose result is represented at the entry closures map returns
coherently at the entry maps. -/
theorem evalReturn_of_exit_id
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {v : Value} {sp r sret : BitVec 64} {m0 : Mem} {c : Config}
    (hExit : EvalExit g N A SL phiF phiC st.store.frames.size st.store.closures.size
      st v sp r sret m0 c)
    (hval : ValueRepr c.σ.mem N phiC sret.toNat v)
    (hW : ReturnWiden (EvalExit g N A SL phiF phiC st.store.frames.size
      st.store.closures.size st v sp r sret m0) N A SL phiF phiC st m0)
    (hwords : ValueWordsTotal m0 sret.toNat) :
    EvalReturn g N A SL phiF phiC st.store.frames.size st.store.closures.size
      st v sp r sret m0 (fun _ _ _ => True) c :=
  have hD : EvalExitD g N A SL phiF phiC st.store.frames.size st.store.closures.size
      st v sp r sret m0 c :=
    ⟨hExit, hW.pres c hExit, ValueWordsTotal.mono (hW.pres c hExit) hwords,
      phiF, phiC, PhiExtends.refl _ _, PhiExtends.refl _ _, hW.surv c hExit⟩
  hD.withReturnRepr
    { frames := PhiExtends.refl _ _
      closures := PhiExtends.refl _ _
      values := fun a w haw => by
        have heq : (a, w) = (sret.toNat, v) := List.mem_singleton.mp haw
        cases heq
        exact hval
      owned := trivial
      survives := fun m' hag => hW.surv c hExit m' (fun k hk => hag k hk) }

#print axioms binOpSem_closuresBounded
#print axioms EpilogueEntryFacts.preEpilogueOwned
#print axioms armReturn_of_facts
#print axioms evalReturn_of_exit_id

#print axioms EvalExitD.coherent_of_bounded
#print axioms EvalExitD.withReturnRepr
#print axioms blockD_v_return
#print axioms EvalReturnIH.forget
#print axioms EvalReturnIH.withMaps
#print axioms EvalIH.coherent_of_bounded

end Vsa.Sim

import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.CallSpec

/-!
# `spliceFold` — the composite Triple for a whole call SEQUENCE

`DeriveCallSeg.callSeg` splices ONE call (`prefix ≫ callee ≫ suffix`).  A real
tail is a SEQUENCE of calls (`strlen ≫ malloc ≫ memcpy ≫ epilogue`), and so far
each such sequence was assembled by a bespoke nested tower of per-callee splice
theorems (`envDefStrlenSplice (envDefMallocSplice (envDefMemcpyFramedSplice
…))`, `EnvDefCompose.lean` — one theorem per callee per sequence).

`SpliceChain` is the dependent list of (staging × callee) hops — a `List`
cannot thread the changing mid-predicates, so the list IS an inductive —
and `spliceFold` is its STRUCTURAL fold into one Triple (elaboration law:
structural recursion, no WF; each step is exactly one `callSeg`).

Step formers:
* `SpliceChain.callStep` — the hop's callee comes from a `CallSpec` (staging
  lands the spec's canonical `EntryP`; the callee Triple is supplied by `Sat`);
* `SpliceChain.stepConseq` — the callee at its own boundary predicates, glued
  by the two seam entailments (the `callSegConseq` shape).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- **A call-splice chain** `P → Q`: zero or more (staging ≫ callee) hops
followed by a final suffix Triple.  The dependent list of a call sequence's
seams — each hop's exit predicate is the next hop's entry. -/
inductive SpliceChain : (Config → Prop) → (Config → Prop) → Prop where
  /-- The final suffix (return marshalling / epilogue / `Triple.rfl`). -/
  | tail {P Q : Config → Prop} (suf : Triple P Q) : SpliceChain P Q
  /-- One call hop: the staging seg lands the callee's entry, the callee
  contract runs, the rest of the chain continues from its exit. -/
  | step {P Mid Post Q : Config → Prop}
      (staging : Triple P Mid) (callee : Triple Mid Post)
      (rest : SpliceChain Post Q) : SpliceChain P Q

/-- **The structural fold**: a whole call sequence collapses to ONE Triple,
one `callSeg` per hop. -/
theorem spliceFold {P Q : Config → Prop} : SpliceChain P Q → Triple P Q
  | .tail suf => suf
  | .step staging callee rest => callSeg staging callee (spliceFold rest)

/-- **`CallSpec` hop former**: the callee is a named `CallSpec` at ghost pack
`g`, its Triple supplied by the spec's `Sat`.  The staging seg's only
obligation is to land the spec's canonical `EntryP`. -/
theorem SpliceChain.callStep {G Res : Type} {P Q : Config → Prop}
    (S : CallSpec G Res) (g : G) (hSat : S.Sat)
    (staging : Triple P (fun c => S.EntryP g c))
    (rest : SpliceChain (S.ExitPost g) Q) : SpliceChain P Q :=
  .step staging (hSat g) rest

/-- **Seam-massaged hop former**: the callee contract at its own boundary
predicates `C_in`/`C_out`, glued by the two entailments (the `callSegConseq`
shape, hop-ified). -/
theorem SpliceChain.stepConseq {P Mid Mid2 Q C_in C_out : Config → Prop}
    (staging : Triple P Mid) (callee : Triple C_in C_out)
    (hin : ∀ c, Mid c → C_in c) (hout : ∀ c, C_out c → Mid2 c)
    (rest : SpliceChain Mid2 Q) : SpliceChain P Q :=
  .step staging (Triple.conseq callee hin hout) rest

/-! ## Demo — the three-call tail shape, one fold

The abstract shape of the strdup tail / `env_define` append path: three
(staging ≫ callee) hops and an epilogue, composed by ONE `spliceFold` instead
of a nested tower of per-callee splice theorems. -/
theorem spliceFoldDemo3
    {P M1 X1 M2 X2 M3 X3 Q : Config → Prop}
    (s1 : Triple P M1) (c1 : Triple M1 X1)
    (s2 : Triple X1 M2) (c2 : Triple M2 X2)
    (s3 : Triple X2 M3) (c3 : Triple M3 X3)
    (epi : Triple X3 Q) : Triple P Q :=
  spliceFold (.step s1 c1 (.step s2 c2 (.step s3 c3 (.tail epi))))

#print axioms spliceFold
#print axioms SpliceChain.callStep
#print axioms SpliceChain.stepConseq
#print axioms spliceFoldDemo3

end Vsa.Sim

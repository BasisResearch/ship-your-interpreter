import Vsa.Sim.CoherentReturn
import Vsa.Sim.SegEffect

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Machine

namespace Vsa.Sim.ReturnRepr

/-- Compose selected maps and retain the left results through the actual second
child's frame. Fresh left closures are bounded by the intermediate store.
Each child may supply its own later-write exclusion footprint. -/
theorem bind
    {N : NativeAddrs} {A : Arena}
    {entryF entryC middleF middleC resultF resultC : Addr → Nat} {nf nc : Nat}
    {middleStore store : Store} {left right : List (Nat × Value)}
    {LeftOwned Owned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    {firstWrites writes : Nat → Prop} {before after : Config} {effect : FrameEffect}
    (first : ReturnRepr N A entryF entryC middleF middleC nf nc
      middleStore left LeftOwned firstWrites before.σ.mem)
    (second : ReturnRepr N A middleF middleC resultF resultC
      middleStore.frames.size middleStore.closures.size store right Owned writes after.σ.mem)
    (hsizeF : nf ≤ middleStore.frames.size) (hsizeC : nc ≤ middleStore.closures.size)
    (hbound : ∀ a v, (a, v) ∈ left → ValueClosuresBounded middleStore.closures.size v)
    (hsteps : FramedSteps effect before after)
    (hheaders : ∀ a v, (a, v) ∈ left → ∀ k, valHeader a k → effect.mem k)
    (hpayloads : ∀ a v, (a, v) ∈ left →
      ValuePayloadCovered effect.mem before.σ.mem a v) :
    ReturnRepr N A entryF entryC resultF resultC nf nc
      store (left ++ right) Owned writes after.σ.mem where
  frames := first.frames.trans (PhiExtends.mono hsizeF second.frames)
  closures := first.closures.trans (PhiExtends.mono hsizeC second.closures)
  values a v hav := by
    rcases List.mem_append.mp hav with hl | hr
    · exact valueRepr_phic_mono (hbound a v hl) second.closures
        (valueRepr_agreeP (fun k hk => (hsteps.frame.mem k hk).symm)
          (hheaders a v hl) (hpayloads a v hl) (first.values a v hl))
    · exact second.values a v hr
  owned := second.owned
  survives := second.survives

#print axioms bind

end Vsa.Sim.ReturnRepr

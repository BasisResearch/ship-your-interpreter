import VsaIris.Vsa.Instance
import Vsa.Lang.Basic

/-!
# Iris route to `Lang.Sim`

At a loaded configuration an interpreter proof supplies initial machine
resources that agree with the configuration (`mr`, `mm`, `VsaOk`) and two
weakest preconditions over them: a total, counted WP (`AdequacyHyp`, via
`twpW`) ending at the specified `(exit, output)` for every specified
behaviour, and a partial, uncounted WP (`AdequacyHypP`, via `wpW`) ending
at an unobservable exit code when no behaviour is specified. `IrisRoute.sim`
turns these into `Lang.Sim` by adequacy.
-/

namespace VsaIris.Lang

open Iris Iris.BI Iris.Std Iris.ProgramLogic
open VsaIris VsaIris.Inst
open Vsa.Machine (Config output)
open Vsa.Lang

/-- A basic update in front of a machine WP is absorbed. -/
theorem wp_of_bupd {GF : BundledGFunctors} [MachGS .hasLC GF] {M : MachineModel}
    (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} : (|==> Wp.W Φ) ⊢ Wp.W Φ :=
  BIUpdateFUpdate.fupd_of_bupd.trans Wp.fupd

/-- The Iris obligations at one loaded configuration. -/
structure RouteAt (GF : BundledGFunctors) [MachGpreS GF] (L : Lang) (live : Nat → Prop)
    (p : L.Prog) (c : Config) where
  mr : NatMap (BitVec 64)
  mm : NatMap (BitVec 8)
  hr : RegAgree (vsaModel live) mr c
  hm : MemAgree (vsaModel live) mm c
  ok : VsaOk live c
  /-- Total WP to each specified behaviour. -/
  term : ∀ e out, L.Spec p e out →
    AdequacyHyp GF (vsaModel live) mr mm (output c.σ) (fun v => v = (e, out))
  /-- Partial WP to an unobservable exit when nothing is specified. -/
  stuck : (¬ ∃ e out, L.Spec p e out) →
    AdequacyHypP GF (vsaModel live) mr mm (output c.σ) (fun v => ¬ L.Obs v.1)

/-- Iris obligations at every loaded, fitting configuration. -/
def IrisRoute (GF : BundledGFunctors) [MachGpreS GF] (L : Lang) (live : Nat → Prop)
    (Loaded : L.Prog → Config → Prop) : Prop :=
  ∀ p c, Loaded p c → L.Fits p → Nonempty (RouteAt GF L live p c)

theorem IrisRoute.sim {GF : BundledGFunctors} [MachGpreS GF] {L : Lang} {live : Nat → Prop}
    {Loaded : L.Prog → Config → Prop} (H : IrisRoute GF L live Loaded) : L.Sim Loaded where
  term p c e out hL hf hs := by
    obtain ⟨R⟩ := H p c hL hf
    obtain ⟨e', out', hh, heq⟩ :=
      vsa_adequacy_exit live c R.mr R.mm R.hr R.hm R.ok _ (R.term e out hs)
    cases heq
    exact hh
  stuck p c hL hf hn := by
    obtain ⟨R⟩ := H p c hL hf
    exact vsa_adequacyP live c R.mr R.mm R.hr R.hm R.ok _ (R.stuck hn)

end VsaIris.Lang

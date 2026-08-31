import Vsa.Sim.EnvGetSpec9

/-!
# Layer 3 — the memory-frame corollary of the immediate-frame `env_get` FOUND case
(`env_get_found_framed`).

`env_get_found_uncond''` (EnvGetSpec9) proves the whole immediate-frame FOUND case
(prologue ≫ scan ≫ strcmp cross-call ≫ HIT-tail) from `FoundSt` + `FrameStackDisj`,
delivering `PC = r`, `a0 = 1`, callee-saveds restored, `sp` popped, and
`ValueRepr m' N φc out (f.vars[iHit].2)`.  But it **drops the memory frame**: its
post only pins the value of `m'` at the out buffer, not what `m'` shares with the
entry memory `m0` everywhere else.

The var-arm call bridge (`rows/EvalVarBridge.lean`, `VarCallLinkage.callee`) needs
that frame to transport the caller's spills and `StoreRepr` across the `env_get`
call: it must know the run wrote **only** the out buffer `[out, out+24)` and the
callee's own stack window `[sp0-64, sp0)` (the seven callee-saved spills).

This corollary supplies exactly that.  Every constituent already pins its own
memory frame — they are simply thrown away inside `env_get_found_uncond'`:

* **prologue** (`env_get_prologue`): `∀ a ∉ [sp0-64, sp0), m9[a]? = m0[a]?`
  (the seven callee-saved spills only touch the fresh 64-byte stack frame),
* **scan** (`scan_iter_from_c60` / `scan_from_c5c_to_hit`): the standing memory is
  `m9` throughout — `HitAt.mem`/`ScanSt.mem` bake in `c.σ.mem = m9`; the strcmp
  cross-calls are read-only, so the scan is a memory identity on `m9`,
* **HIT-tail** (`env_get_hit_tail`): `∀ a ∉ [out, out+24), m'[a]? = m9[a]?`
  (the three-word copy into the out buffer is the only write).

Composing the two disjoint-frame facts by transitivity gives

  `∀ a ∉ ([out, out+24) ∪ [sp0-64, sp0)), m'[a]? = m0[a]?`,

the additive-frame post `env_get_found_framed`.  The statement `env_get_found_uncond''`
is UNCHANGED; this is a strict re-assembly that keeps the frame (the same pattern as
`strlen_spec_framed`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Store Value)
open Vsa.Alloc
open Vsa.Sim.Code (Env_getLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The memory-frame footprint of the immediate-frame `env_get` FOUND run:
`a` lies OUTSIDE the out buffer `[out, out+24)` AND outside the callee's fresh
64-byte stack frame `[sp0-64, sp0)`.  Everywhere in this set the run is a memory
identity (`m'[a]? = m0[a]?`). -/
def EnvGetFootprint (out sp0 : BitVec 64) : Nat → Prop :=
  fun a => ¬ (out.toNat ≤ a ∧ a < out.toNat + 24) ∧
           ¬ ((sp0 - 64#64).toNat ≤ a ∧ a < (sp0 - 64#64).toNat + 64)

/-- **Immediate-frame `env_get` FOUND case, memory-frame–carrying.**

Identical premises and register/`ValueRepr` post to `env_get_found_uncond''`, plus
the additive memory-frame clause: the whole run writes ONLY `[out, out+24)` (the
returned value) and `[sp0-64, sp0)` (the callee's own stack spills); everywhere else
`m' = m0` byte-for-byte.  This is the frame `VarCallLinkage.callee`'s suffix consumes
to transport the caller's spills and `StoreRepr` across the call.

The proof re-runs the FOUND assembly (prologue ≫ scan ≫ HIT-tail) exactly as
`env_get_found_uncond'`, but captures the prologue's spill frame `houtside` and the
HIT-tail's out-buffer frame `hframe'` (both dropped as `_` inside
`env_get_found_uncond'`) and composes them by transitivity through the scan's
memory identity `m9`. -/
theorem env_get_found_framed
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (nameStr : String) (iw : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config)
    (hFS : FoundSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
      f N φf φc m0 c)
    (hD : FrameStackDisj env name sp0 pn nameStr f m0) :
    ∃ (c' : Config) (m' : Mem) (iHit : Nat) (hi : iHit < f.vars.length),
      Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.regs.get? Register.PC = some r ∧
      c'.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x1 = some r ∧
      c'.σ.regs.get? Register.x2 = some ((sp0 - 64#64) + 64#64) ∧
      c'.σ.regs.get? Register.x8 = some r8 ∧
      c'.σ.regs.get? Register.x9 = some r9 ∧
      c'.σ.regs.get? Register.x18 = some r18 ∧
      c'.σ.regs.get? Register.x19 = some r19 ∧
      c'.σ.regs.get? Register.x20 = some r20 ∧
      c'.σ.regs.get? Register.x21 = some r21 ∧
      c'.σ.mem = m' ∧ Env_getLoaded m' ∧
      ValueRepr m' N φc out.toNat (f.vars[iHit]'hi).2 ∧
      -- the returned index is the FIRST name-hit for `nameStr` (the scan matched it
      -- and passed all earlier slots); this pins `iHit` = the least-match index, so a
      -- caller with its own least-match witness `iw` reconciles `iHit = iw`.
      (f.vars[iHit]'hi).1 = nameStr ∧
      (∀ j, (hj : j < f.vars.length) → j < iHit → f.vars[j].1 ≠ nameStr) ∧
      -- THE memory frame: the run wrote only `[out, out+24) ∪ [sp0-64, sp0)`.
      (∀ a : Nat, EnvGetFootprint out sp0 a → m'[a]? = m0[a]?) := by
  -- run the verified prologue to the body entry `c60`, KEEPING its spill frame.
  obtain ⟨c60, m9, hsP, hGP, htickP, hpcP, h20P, h19P, h21P, h18P, h9P, h8P, hraP, hspP,
    hmemP, hcodeP, s56, s48, s40, s32, s24, s16, s8, houtside, _hsoutP⟩ :=
    env_get_prologue env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn f N φf φc m0 c hFS.base
  -- build the scan-ready bundle over m9 from FoundSt + FrameStackDisj (as in `''`).
  obtain ⟨g0, hSt60, hframe9, hloaded9, hgeom9⟩ :=
    foundSt_scanReady env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
      f N φf φc m0 c hFS hD c60 m9 hpcP h20P h19P h21P h18P h9P h8P hraP hspP hmemP hGP htickP
      hcodeP s56 s48 s40 s32 s24 s16 s8 houtside
  -- normalize `0 < f.vars.length` (iw witnesses it)
  have h0lt : 0 < f.vars.length := Nat.lt_of_le_of_lt (Nat.zero_le iw) hFS.iwLt
  -- run the from-c60 first body: HIT (i=0) or MISS (advance to ScanSt@c5c i=1)
  obtain ⟨c1, hs1, hdisj1⟩ :=
    scan_iter_from_c60 g0 env name out (BitVec.ofNat 64 len) (BitVec.ofNat 64 pn) r0
      (sp0 - 64#64) 0 f nameStr N φf φc m9 c60 hSt60 (by intro j hj hji; omega) h0lt
  -- reach a register-carrying HitAt at the first-match index
  obtain ⟨cHit, iHit, hsHit, hHit⟩ :
      ∃ (cHit : Config) (iHit : Nat), Steps c60 cHit ∧
        HitAt env out (sp0 - 64#64) iHit f nameStr m9 cHit := by
    rcases hdisj1 with ⟨g1, hSt1, hfm1⟩ | hHit0
    · have h1le : 1 ≤ iw := by
        rcases Nat.eq_zero_or_pos iw with h | h
        · subst h; exact absurd hFS.iwHit (hfm1 0 h0lt (by omega))
        · omega
      obtain ⟨cHit, iHit, hs2, hHit⟩ :=
        scan_from_c5c_to_hit env name out (BitVec.ofNat 64 len) (BitVec.ofNat 64 pn) (sp0 - 64#64)
          f nameStr N φf φc m9 iw hFS.iwLt hFS.iwHit iw g1 1 c1 hSt1 hfm1 h1le (by omega)
      exact ⟨cHit, iHit, hs1.trans hs2, hHit⟩
    · exact ⟨c1, 0, hs1, hHit0⟩
  -- repackage AtHit → HitTailSt
  obtain ⟨pv, w0, w1, w2, hHitTail⟩ :=
    hitAt_to_hitTail env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw iHit
      f N φf φc m0 m9 cHit c hFS hframe9 hHit.mem.symm hHit hloaded9
      (fun pv hpv => hgeom9 pv hpv iHit hHit.ilt) s56 s48 s40 s32 s24 s16 s8
  -- run the verified HIT tail, KEEPING its out-buffer memory frame `hframe'`.
  obtain ⟨c', m', hsT, hG, htick, hpc, ha0, hra, hsp', hx8, hx9, hx18, hx19, hx20, hx21,
    hmem', hcode', hvr, hframe', _hsoutT⟩ :=
    env_get_hit_tail (cHit.σ.regs.get?) env out (sp0 - 64#64) r r0 r8 r9 r18 r19 r20 r21 iHit pv w0 w1 w2
      f N φf φc m9 cHit hHit.ilt hHitTail
  refine ⟨c', m', iHit, hHit.ilt, (hsP.trans hsHit).trans hsT, hG, htick, hpc, ha0, hra, hsp',
    hx8, hx9, hx18, hx19, hx20, hx21, hmem', hcode', hvr, hHit.hit, hHit.firstMatch, ?_⟩
  -- compose the two disjoint-window frames through the scan's memory identity `m9`.
  -- `hframe'` : `∀ a ∉ [out,out+24), m'[a]? = m9[a]?`   (HIT-tail; m9 is its m0)
  -- `houtside` : `∀ a ∉ [sp0-64,sp0), m9[a]? = m0[a]?`  (prologue)
  intro a ha
  obtain ⟨haOut, haSp⟩ := ha
  rw [hframe' a haOut, houtside a haSp]

#print axioms env_get_found_framed

end Vsa.Sim

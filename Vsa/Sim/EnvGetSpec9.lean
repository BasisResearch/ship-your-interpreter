import Vsa.Sim.EnvGetSpec8

/-!
# Layer 3 — discharging `hScanReady`: the memory-transport of the scan-ready
representation across the prologue's callee-saved spills (`env_get_found_uncond''`).

`env_get_found_uncond'` (EnvGetSpec8) proved the FULL immediate-frame FOUND case
modulo ONE residual, `hScanReady`: the transport of the frame's
`FrameRepr`/`ScanNames`/per-slot geometry from the entry memory `m0` across the
prologue's seven callee-saved spills into the fresh stack frame `[sp0-64, sp0)` to
the post-prologue scan memory `m9`.

The prologue (`env_get_prologue`, EnvGetSpec7) proves the memory-agreement fact

  `∀ a ∉ [sp0-64, sp0), m9[a]? = m0[a]?`   (the spills only touch the stack frame),

i.e. `AgreeP P m0 m9` for `P a := ¬((sp0-64).toNat ≤ a ∧ a < (sp0-64).toNat + 64)`.
The heap/arena frame region (the `Env` header, the names/values arrays, and the
name/value payload strings) plus the strcmp mask rodata are **disjoint** from that
stack spill window — a real, honest heap-vs-stack side condition, captured once in
`FrameStackDisj`.  Every read the scan-ready package makes lands outside the spill
window, so it transfers `m0 → m9` byte-for-byte via the existing `*_agreeP`
agreement lemmas (`frameRepr_agreeP`, `cstring_agreeP`, `read64_agreeP`,
`read32_agreeP` from `ReprSurvival`).

`foundSt_scanReady` performs that transport; `env_get_found_uncond''` feeds it into
`env_get_found_uncond'`, yielding the immediate-frame FOUND Triple with NO
scan-readiness hypothesis — only the honest caller-facts (`FoundSt`) plus the ONE
documented heap-vs-stack disjointness geometry (`FrameStackDisj`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
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

/-! ## The spill-window footprint predicate

`OutsideSpill sp0 a` holds iff `a` lies OUTSIDE the fresh 64-byte stack frame
`[sp0-64, sp0)` the prologue's seven spills write.  The prologue's
memory-agreement output is exactly `AgreeP (OutsideSpill sp0) m0 m9`. -/
def OutsideSpill (sp0 : BitVec 64) : Nat → Prop :=
  fun a => ¬ ((sp0 - 64#64).toNat ≤ a ∧ a < (sp0 - 64#64).toNat + 64)

/-- `CStr` is functional in a fixed memory. -/
theorem cstr_unique_eg9 (m : Mem) (p : Nat) (cs cs' : List Char)
    (h : CStr m p cs) (h' : CStr m p cs') : cs = cs' := by
  induction h generalizing cs' with
  | @nil a hnil =>
    cases h' with
    | nil _ => rfl
    | @cons a' b' cs'' hb' hbne' hblt' hrest' =>
      rw [hnil] at hb'; injection hb' with hb'; exact absurd hb'.symm hbne'
  | @cons a b cs hb hbne hblt hrest ih =>
    cases h' with
    | nil hnil' => rw [hnil'] at hb; injection hb with hb; exact absurd hb.symm hbne
    | @cons a' b'' cs'' hb'' hbne'' hblt'' hrest'' =>
      rw [hb''] at hb; injection hb with hb; subst hb
      rw [ih cs'' hrest'']

/-- The prologue's `∀ a ∉ [sp0-64, sp0), m9[a]? = m0[a]?` is `AgreeP` over
`OutsideSpill sp0`. -/
theorem agreeP_of_prologue {sp0 : BitVec 64} {m0 m9 : Mem}
    (h : ∀ a : Nat, ¬ ((sp0 - 64#64).toNat ≤ a ∧ a < (sp0 - 64#64).toNat + 64) →
      m9[a]? = m0[a]?) :
    AgreeP (OutsideSpill sp0) m0 m9 :=
  fun a ha => (h a ha).symm

/-! ## The honest heap-vs-stack disjointness carrier (`FrameStackDisj`)

The frame's entire read footprint at memory `m0` — the 32-byte `Env` header
`[env, env+32)`, each 8-byte name-pointer slot `[pn+8i, pn+8i+8)`, each name
string `[qn, qn + name.length]`, each 24-byte value header `[pv+24i, pv+24i+24)`,
each inner value string `[pval, pval + s.length]` — and the strcmp mask rodata
`[maskAddr, maskAddr+8)` are all disjoint from the fresh stack spill window
`[sp0-64, sp0)`.  This is the heap-frame-vs-C-stack disjointness from the memory
map: the heap arena and rodata sit above `0x80000000` in fixed regions, the C
stack frame is a fresh window the caller allocated below them; they never overlap.

Stated per-read (over the `m0` witnesses `pn`/`pv`/`qn`/`pval`) in exactly the
shape `frameRepr_agreeP`/`cstring_agreeP` consume, so the transport discharges each
side condition directly from the corresponding field. -/
structure FrameStackDisj
    (env name sp0 : BitVec 64) (pn : Nat) (nameStr : String)
    (f : Vsa.While.Frame) (m0 : Mem) : Prop where
  -- env header `[env, env+32)`
  hdr : ∀ k, envHeader env.toNat k → OutsideSpill sp0 k
  -- name-pointer slots + value headers (footprints keyed to the `m0` witnesses)
  slots : ∀ pn' pv, read64 m0 (env.toNat + 8) = some pn' → read64 m0 (env.toNat + 16) = some pv →
    ∀ i, i < f.vars.length →
      (∀ k, k < 8 → OutsideSpill sp0 (pn' + 8 * i + k)) ∧
      (∀ k, valHeader (pv + 24 * i) k → OutsideSpill sp0 k)
  -- name strings `[qn, qn + name.length]`
  names : ∀ pn' pv, read64 m0 (env.toNat + 8) = some pn' → read64 m0 (env.toNat + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) → ∀ qn, read64 m0 (pn' + 8 * i) = some qn →
      (∀ k, k ≤ (f.vars[i].1).length → OutsideSpill sp0 (qn + k))
  -- inner value strings `[pval, pval + s.length]`
  valstr : ∀ pn' pv, read64 m0 (env.toNat + 8) = some pn' → read64 m0 (env.toNat + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) →
      ∀ (pval : Nat) (s : String), read64 m0 (pv + 24 * i + 8) = some pval →
        (∀ k, k ≤ s.length → OutsideSpill sp0 (pval + k))
  -- the query `name` argument's own string `[name.toNat, name.toNat + nameStr.length]`
  query : ∀ k, k ≤ nameStr.length → OutsideSpill sp0 (name.toNat + k)
  -- strcmp mask rodata `[maskAddr, maskAddr+8)`
  mask : ∀ k, k < 8 → OutsideSpill sp0 (maskAddr + k)
  -- strcmp text `[0x80006ea0, 0x80006fcc)`
  strcmpCode : ∀ k, 0x80006ea0 ≤ k → k < 0x80006fcc → OutsideSpill sp0 k

theorem maskPinned_outsideSpill {sp0 : BitVec 64} {m0 m9 : Mem}
    (hA : AgreeP (OutsideSpill sp0) m0 m9)
    (hmask : ∀ k, k < 8 → OutsideSpill sp0 (maskAddr + k))
    (h : MaskPinned m0) : MaskPinned m9 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hA maskAddr (by simpa using hmask 0 (by omega))]; exact h0
  · rw [← hA (maskAddr + 1) (hmask 1 (by omega))]; exact h1
  · rw [← hA (maskAddr + 2) (hmask 2 (by omega))]; exact h2
  · rw [← hA (maskAddr + 3) (hmask 3 (by omega))]; exact h3
  · rw [← hA (maskAddr + 4) (hmask 4 (by omega))]; exact h4
  · rw [← hA (maskAddr + 5) (hmask 5 (by omega))]; exact h5
  · rw [← hA (maskAddr + 6) (hmask 6 (by omega))]; exact h6
  · rw [← hA (maskAddr + 7) (hmask 7 (by omega))]; exact h7

theorem strcmpLoaded_outsideSpill {sp0 : BitVec 64} {m0 m9 : Mem}
    (hA : AgreeP (OutsideSpill sp0) m0 m9)
    (hcode : ∀ k, 0x80006ea0 ≤ k → k < 0x80006fcc → OutsideSpill sp0 k)
    (h : StrcmpLoaded m0) : StrcmpLoaded m9 := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.strcmpChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [← hA _ (hcode _ (by decide) (by decide))]; simp_all only [])
  · simp only [Vsa.Sim.Code.strcmpChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [← hA _ (hcode _ (by decide) (by decide))]; simp_all only [])
  · simp only [Vsa.Sim.Code.strcmpChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (rw [← hA _ (hcode _ (by decide) (by decide))]; simp_all only [])
  · simp only [Vsa.Sim.Code.strcmpChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (rw [← hA _ (hcode _ (by decide) (by decide))]; simp_all only [])
  · simp only [Vsa.Sim.Code.strcmpChunk4] at c4 ⊢
    repeat' apply And.intro
    all_goals (rw [← hA _ (hcode _ (by decide) (by decide))]; simp_all only [])

/-- The scan carrier survives the prologue spills. -/
theorem scanNames_agreeP
    (env name sp0 : BitVec 64) (pn : Nat) (nameStr : String)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 m9 : Mem)
    (hA : AgreeP (OutsideSpill sp0) m0 m9)
    (hD : FrameStackDisj env name sp0 pn nameStr f m0)
    (hF : FrameRepr m0 N φf φc env.toNat f)
    (hpn0 : read64 m0 (env.toNat + 8) = some pn)
    (hS : ScanNames m0 pn name nameStr f) :
    ScanNames m9 pn name nameStr f := by
  obtain ⟨_, _, ⟨pn', pv, hpn', hpv, _⟩, _⟩ := hF
  have hpnEq : pn' = pn := by
    rw [hpn0] at hpn'
    exact Option.some.inj hpn'.symm
  subst pn'
  have slotP : ∀ i, i < f.vars.length → ∀ k, k < 8 →
      OutsideSpill sp0 (pn + 8 * i + k) :=
    fun i hi => (hD.slots pn pv hpn0 hpv i hi).1
  refine
    { maskPinned := maskPinned_outsideSpill hA hD.mask hS.maskPinned,
      nameCStr := cstring_agreeP hA hS.nameCStr hD.query,
      nameRegB := ?_, nameRegW := ?_, bindPtr := ?_, bindRegB := ?_, bindRegW := ?_,
      slotLo := hS.slotLo, slotHi := hS.slotHi, slotHtif := hS.slotHtif,
      slotAlign := hS.slotAlign }
  · intro cs hcs9
    obtain ⟨cs0, hcs0, hs0⟩ := hS.nameCStr
    have hlen0 : cs0.length = nameStr.length := by rw [hs0, String.length_ofList]
    have hcs0' : CStr m9 name.toNat cs0 :=
      cstr_agreeP hA hcs0 (fun k hk => hD.query k (by omega))
    have heq : cs = cs0 := cstr_unique_eg9 m9 name.toNat cs cs0 hcs9 hcs0'
    subst cs
    exact hS.nameRegB cs0 hcs0
  · intro cs hcs9
    obtain ⟨cs0, hcs0, hs0⟩ := hS.nameCStr
    have hlen0 : cs0.length = nameStr.length := by rw [hs0, String.length_ofList]
    have hcs0' : CStr m9 name.toNat cs0 :=
      cstr_agreeP hA hcs0 (fun k hk => hD.query k (by omega))
    have heq : cs = cs0 := cstr_unique_eg9 m9 name.toNat cs cs0 hcs9 hcs0'
    subst cs
    exact hS.nameRegW cs0 hcs0
  · intro i hi
    obtain ⟨q, hq, hqstr⟩ := hS.bindPtr i hi
    refine ⟨q, ?_, cstring_agreeP hA hqstr (hD.names pn pv hpn0 hpv i hi q hq)⟩
    rw [← read64_agreeP hA (slotP i hi)]
    exact hq
  · intro i hi q hq9 cs hcs9
    obtain ⟨q0, hq0, cs0, hcs0, hs0⟩ := hS.bindPtr i hi
    have hq09 : read64 m9 (pn + 8 * i) = some q0 := by
      rw [← read64_agreeP hA (slotP i hi)]
      exact hq0
    have hqq : q0 = q := by rw [hq9] at hq09; exact Option.some.inj hq09.symm
    subst q0
    have hlen0 : cs0.length = (f.vars[i].1).length := by
      rw [hs0, String.length_ofList]
    have hcs0' : CStr m9 q cs0 :=
      cstr_agreeP hA hcs0 (fun k hk => hD.names pn pv hpn0 hpv i hi q hq0 k (by omega))
    have heq : cs = cs0 := cstr_unique_eg9 m9 q cs cs0 hcs9 hcs0'
    subst cs
    exact hS.bindRegB i hi q hq0 cs0 hcs0
  · intro i hi q hq9 cs hcs9
    obtain ⟨q0, hq0, cs0, hcs0, hs0⟩ := hS.bindPtr i hi
    have hq09 : read64 m9 (pn + 8 * i) = some q0 := by
      rw [← read64_agreeP hA (slotP i hi)]
      exact hq0
    have hqq : q0 = q := by rw [hq9] at hq09; exact Option.some.inj hq09.symm
    subst q0
    have hlen0 : cs0.length = (f.vars[i].1).length := by
      rw [hs0, String.length_ofList]
    have hcs0' : CStr m9 q cs0 :=
      cstr_agreeP hA hcs0 (fun k hk => hD.names pn pv hpn0 hpv i hi q hq0 k (by omega))
    have heq : cs = cs0 := cstr_unique_eg9 m9 q cs cs0 hcs9 hcs0'
    subst cs
    exact hS.bindRegW i hi q hq0 cs0 hcs0

/-- `FrameRepr` survives the prologue spills under `FrameStackDisj`. -/
theorem frameRepr_outsideSpill
    (env name sp0 : BitVec 64) (pn : Nat) (nameStr : String)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 m9 : Mem)
    (hA : AgreeP (OutsideSpill sp0) m0 m9)
    (hD : FrameStackDisj env name sp0 pn nameStr f m0)
    (hF : FrameRepr m0 N φf φc env.toNat f) :
    FrameRepr m9 N φf φc env.toNat f :=
  frameRepr_agreeP hA hD.hdr hD.slots hD.names hD.valstr hF

/-- The per-value-slot read facts in `FoundSt` survive the prologue spills. -/
theorem foundPvVals_agreeP
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (nameStr : String) (iw : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 m9 : Mem) (c : Config)
    (hFS : FoundSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
      f N φf φc m0 c)
    (hA : AgreeP (OutsideSpill sp0) m0 m9)
    (hD : FrameStackDisj env name sp0 pn nameStr f m0) :
    ∀ pv, read64 m9 (env.toNat + 16) = some pv →
      ∀ i, i < f.vars.length →
        (∃ w0 w1 w2, read64 m9 (pv + 24 * i) = some w0 ∧
          read64 m9 (pv + 24 * i + 8) = some w1 ∧
          read64 m9 (pv + 24 * i + 16) = some w2) ∧
        0x80000000 ≤ pv + 24 * i ∧ pv + 24 * i + 24 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ pv + 24 * i ∧ (pv + 24 * i) % 8 = 0 ∧
        pv + 24 * i + 24 < 2^64 ∧ pv + 24 * i < 2^64 ∧
        (pv + 24 * i + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * i) ∧
        (∀ (p : Nat) (s : String), read64 m9 (pv + 24 * i + 8) = some p →
          ∀ k, k ≤ s.length → (p + k < out.toNat ∨ out.toNat + 24 ≤ p + k)) := by
  intro pv hpv9 i hi
  have henv16 : ∀ k, k < 8 → OutsideSpill sp0 (env.toNat + 16 + k) :=
    fun k hk => hD.hdr _ ⟨by omega, by omega⟩
  have hpv0 : read64 m0 (env.toNat + 16) = some pv := by
    rw [read64_agreeP hA henv16]
    exact hpv9
  obtain ⟨⟨w0, w1, w2, hw0, hw1, hw2⟩, hlo, hhi, hwin, halign, hnw, hpvnw,
    hdisj, hpay⟩ := hFS.pvVals pv hpv0 i hi
  have hvhdr := (hD.slots pn pv hFS.base.read_pn hpv0 i hi).2
  refine ⟨⟨w0, w1, w2, ?_, ?_, ?_⟩, hlo, hhi, hwin, halign, hnw, hpvnw, hdisj, ?_⟩
  · rw [← read64_agreeP hA (fun k hk => hvhdr _ ⟨by omega, by omega⟩)]
    exact hw0
  · rw [← read64_agreeP hA (valHeader_read64_off8 hvhdr)]
    exact hw1
  · rw [← read64_agreeP hA (valHeader_read64_off16 hvhdr)]
    exact hw2
  · intro p s hp9 k hk
    have hp0 : read64 m0 (pv + 24 * i + 8) = some p := by
      rw [read64_agreeP hA (valHeader_read64_off8 hvhdr)]
      exact hp9
    exact hpay p s hp0 k hk

/-- Build the post-prologue scan state from `FoundSt` and the honest spill
disjointness assumptions.  This discharges `env_get_found_uncond'`'s last residual. -/
theorem foundSt_scanReady
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (nameStr : String) (iw : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c0 : Config)
    (hFS : FoundSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
      f N φf φc m0 c0)
    (hD : FrameStackDisj env name sp0 pn nameStr f m0)
    (c60 : Config) (m9 : Mem)
    (hpc : c60.σ.regs.get? Register.PC = some (0x80002c60#64 : BitVec 64))
    (h20 : c60.σ.regs.get? Register.x20 = some env)
    (h19 : c60.σ.regs.get? Register.x19 = some name)
    (h21 : c60.σ.regs.get? Register.x21 = some out)
    (h18 : c60.σ.regs.get? Register.x18 = some (BitVec.ofNat 64 len))
    (h9 : c60.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 pn))
    (h8 : c60.σ.regs.get? Register.x8 = some (0#64 : BitVec 64))
    (h1 : c60.σ.regs.get? Register.x1 = some r0)
    (h2 : c60.σ.regs.get? Register.x2 = some (sp0 - 64#64))
    (hmem : c60.σ.mem = m9) (hG : GoodState c60.σ) (htick : c60.tick < 2)
    (hloadedG : Env_getLoaded m9)
    (_hs56 : read64 m9 ((sp0 - 64#64).toNat + 56) = some r0.toNat)
    (_hs48 : read64 m9 ((sp0 - 64#64).toNat + 48) = some r8.toNat)
    (_hs40 : read64 m9 ((sp0 - 64#64).toNat + 40) = some r9.toNat)
    (_hs32 : read64 m9 ((sp0 - 64#64).toNat + 32) = some r18.toNat)
    (_hs24 : read64 m9 ((sp0 - 64#64).toNat + 24) = some r19.toNat)
    (_hs16 : read64 m9 ((sp0 - 64#64).toNat + 16) = some r20.toNat)
    (_hs8 : read64 m9 ((sp0 - 64#64).toNat + 8) = some r21.toNat)
    (houtside : ∀ a : Nat,
      ¬ ((sp0 - 64#64).toNat ≤ a ∧ a < (sp0 - 64#64).toNat + 64) →
        m9[a]? = m0[a]?) :
    ∃ (g0 : (R : Register) → Option (RegisterType R)),
      ScanSt g0 (0x80002c60#64) env name out (BitVec.ofNat 64 len)
        (BitVec.ofNat 64 pn) r0 (sp0 - 64#64) 0 f nameStr N φf φc m9 c60 ∧
      FrameRepr m9 N φf φc env.toNat f ∧ Env_getLoaded m9 ∧
      (∀ pv, read64 m9 (env.toNat + 16) = some pv →
        ∀ i, i < f.vars.length →
          (∃ w0 w1 w2, read64 m9 (pv + 24 * i) = some w0 ∧
            read64 m9 (pv + 24 * i + 8) = some w1 ∧
            read64 m9 (pv + 24 * i + 16) = some w2) ∧
          0x80000000 ≤ pv + 24 * i ∧ pv + 24 * i + 24 ≤ 0x100000000 ∧
          tohostAddr + 16 ≤ pv + 24 * i ∧ (pv + 24 * i) % 8 = 0 ∧
          pv + 24 * i + 24 < 2^64 ∧ pv + 24 * i < 2^64 ∧
          (pv + 24 * i + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * i) ∧
          (∀ (p : Nat) (s : String), read64 m9 (pv + 24 * i + 8) = some p →
            ∀ k, k ≤ s.length → (p + k < out.toNat ∨ out.toNat + 24 ≤ p + k))) := by
  let g0 : (R : Register) → Option (RegisterType R) := fun R => c60.σ.regs.get? R
  have hA : AgreeP (OutsideSpill sp0) m0 m9 := agreeP_of_prologue houtside
  have hframe9 : FrameRepr m9 N φf φc env.toNat f :=
    frameRepr_outsideSpill env name sp0 pn nameStr f N φf φc m0 m9 hA hD hFS.base.frame
  have hnames9 : ScanNames m9 pn name nameStr f :=
    scanNames_agreeP env name sp0 pn nameStr f N φf φc m0 m9 hA hD hFS.base.frame
      hFS.base.read_pn hFS.namesC
  have hloadedS9 : StrcmpLoaded m9 := by
    exact strcmpLoaded_outsideSpill hA hD.strcmpCode hFS.loadedS
  have hcount : (BitVec.ofNat 64 len).toNat = f.vars.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hFS.base.lenSmall; omega),
      hFS.base.len_eq]
  refine ⟨g0, ?_, hframe9, hloadedG,
    foundPvVals_agreeP env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
      f N φf φc m0 m9 c0 hFS hA hD⟩
  refine
    { good := hG, loadedG := by rw [hmem]; exact hloadedG,
      loadedS := by rw [hmem]; exact hloadedS9, mem := hmem, pc := hpc,
      env4 := h20, name3 := h19, out5 := h21, count2 := h18,
      cursor1 := by simpa using h9, idx0 := by simpa using h8,
      ra := h1, sp2 := h2, minstret := hG.minstret, tick := htick,
      frame := hframe9,
      names := by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hFS.pnSmall] using hnames9,
      count_eq := hcount,
      ile := Nat.zero_le _, ghost := fun _ _ => rfl }

/-- Immediate-frame `env_get` FOUND case with no scan-boundary hypothesis. -/
theorem env_get_found_uncond''
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
      ValueRepr m' N φc out.toNat (f.vars[iHit]'hi).2 := by
  apply env_get_found_uncond' env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
    f N φf φc m0 c hFS
  intro c60 m9 hpc h20 h19 h21 h18 h9 h8 h1 h2 hmem hG htick hloaded
    hs56 hs48 hs40 hs32 hs24 hs16 hs8 houtside
  exact foundSt_scanReady env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
    f N φf φc m0 c hFS hD c60 m9 hpc h20 h19 h21 h18 h9 h8 h1 h2 hmem hG htick
    hloaded hs56 hs48 hs40 hs32 hs24 hs16 hs8 houtside

#print axioms scanNames_agreeP
#print axioms frameRepr_outsideSpill
#print axioms foundPvVals_agreeP
#print axioms foundSt_scanReady
#print axioms env_get_found_uncond''

end Vsa.Sim

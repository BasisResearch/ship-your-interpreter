import Vsa.Sim.BlockPilot
import Vsa.Sim.StrlenSpec
import Vsa.Sim.MemcpySpecFramed

/-!
# `CallSpec` — the calling-convention layer (the function-verification exponentiator)

Every call splice so far (the strdup tail, the concat C-block, `env_define`
append/grow, `env_new`, the EX_FN malloc splice) re-proves per seam: (a) ABI
frame transport, (b) arena-invariant survival, (c) code-pin survival, (d)
spill-window disjointness — each as its own hand-threaded hypothesis family.
And every callee contract is a bespoke shape (`strlen_pre`/`strlen_post`,
`PreDispatch`, `MallocContract.spec`'s inline lambdas), so each seam needs hand
marshalling; `rows/ConcatSeams.lean` had to DUPLICATE `MallocContract`'s
pre/post as `ConcatMallocPre`/`ConcatMallocPost` because the shapes have no
reusable names.  Finally, 2–3 of this campaign's statement falsities were
frame/clobber bugs (the `StrcpyContract` `NotWritten` alias; the strdup
s0-reseat ghost) — representable only because clobber sets were implicit.

`CallSpec` names the ONE canonical ABI-call shape every surveyed contract
shares, as DATA with explicit clobber set and footprint:

  ENTRY: `GoodState` + `tick<2` + `PC = entry` + arg-register pins +
    `x1 = ret` (4-aligned) + the ABI callee-saved ghost tie + `mem = mem0` +
    the instance's domain side conditions;
  EXIT:  `GoodState` + `tick<2` + `PC = ret` + result-register pins (functions
    of ghosts + an existential result witness) + the CLOBBER-RESTRICTED ABI tie
    + the memory transform (reads outside `foot` unchanged) + the domain post.

The ghost pack `G` carries all per-call ghosts INCLUDING the return address and
the ABI register ghost (memcpy's `PreDispatch.hframe` ties `NotWrittenB ⊇
AbiPreserved` registers to the ghost, so the side conditions must be able to
mention it — hence `ghost : G → …` is a projection, not an outer quantifier).

Three THIN pilot instances prove the EXISTING theorems inhabit their CallSpecs
(`strlen_spec_framed`, `MallocContract.spec`, `memcpy_spec_framed_byte`) — the
existing theorems are untouched.

Expressiveness notes (the audit, see `experiments/logs/wave36-callspec.md`):
* `foot` must be `Nat → Prop`, not a region list — malloc's footprint is
  `privFoot ∪ stack-window` with `privFoot` abstract.
* `EntryP` pins `c.σ.mem = mem0 g` — the memory-transform baseline IS the entry
  memory.  memcpy's `PreDispatch` is laxer (only `meminv`-outside agreement
  with `m0`); the pilot instance is correspondingly narrower, which loses
  nothing at real use sites (they all instantiate `m0` := the entry memory).
* malloc's success-or-NULL post disjunction: `Res := Nat` with `0` encoding
  NULL — ONE pin shape `x10 = ofNat res` covers both branches, and the
  disjunction lives in `postSide`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.RuntimeRepr (Arena)
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.Alloc
open Vsa.MemRepr (CString)
open Vsa.Sim.Code (StrlenLoaded MemcpyLoaded)

namespace Vsa.Sim

/-! ## The spec record — DATA, with explicit clobber set and footprint -/

/-- **A calling-convention contract for one callee**, as data.  `G` is the ghost
pack (all per-call ghosts: arguments, entry memory, return address, ABI register
ghost, side-condition proofs); `Res` is the result-witness sort bound
existentially in the exit (e.g. the malloc pointer, memcpy's exit register
ghost; `Unit` when the result is ghost-determined).

The two fields the falsity lesson demands be EXPLICIT data:
* `clobber` — the ABI-preserved registers the callee is nonetheless allowed to
  change (`fun _ => false` for a true ABI callee; `x8` for an s0-reseating
  staging span, cf. `AbiExceptS0`).  A wrong clobber set is now a visible wrong
  LITERAL, not a mis-threaded ghost.
* `foot` — the callee's memory write footprint; the exit's memory transform
  says reads outside it are unchanged from `mem0`. -/
structure CallSpec (G : Type) (Res : Type) where
  /-- The callee's entry PC. -/
  entry : G → BitVec 64
  /-- The return address (`x1` at entry, `PC` at exit). -/
  ret : G → BitVec 64
  /-- The ABI register ghost the entry/exit ties are keyed to. -/
  ghost : G → (R : Register) → Option (RegisterType R)
  /-- Entry argument-register pins (`GRegs`-style, consumed via `GHolds`). -/
  prePins : G → GRegs
  /-- The entry memory (the memory-transform baseline). -/
  mem0 : G → Std.ExtHashMap Nat (BitVec 8)
  /-- Domain-specific entry facts (code pins, `CString`, `AInv`, `StackOK`, …). -/
  preSide : G → Config → Prop
  /-- EXPLICIT clobber set: ABI-preserved registers the callee may change. -/
  clobber : Register → Bool
  /-- The callee's memory write footprint. -/
  foot : G → Nat → Prop
  /-- Exit result-register pins, as functions of ghosts + the result witness. -/
  postPins : G → Res → GRegs
  /-- The domain post (result facts; e.g. malloc's success-or-NULL disjunction). -/
  postSide : G → Res → Config → Prop

namespace CallSpec

variable {G Res : Type}

/-- **The canonical ABI-call entry predicate** of a `CallSpec` (named fields per
CLAUDE.md R6 — never an anonymous ∧-tower). -/
structure EntryP (S : CallSpec G Res) (g : G) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (S.entry g)
  args : GHolds c.σ (S.prePins g)
  ra : c.σ.regs.get? Register.x1 = some (S.ret g)
  raAligned : (S.ret g).toNat % 4 = 0
  abi : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = S.ghost g R
  mem : c.σ.mem = S.mem0 g
  side : S.preSide g c

/-- **The canonical ABI-call exit predicate**, at result witness `res`.  The
register tie is CLOBBER-RESTRICTED: every ABI-preserved register OUTSIDE the
spec's explicit clobber set is tied back to the entry ghost. -/
structure ExitP (S : CallSpec G Res) (g : G) (res : Res) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (S.ret g)
  rets : GHolds c.σ (S.postPins g res)
  frame : ∀ R, AbiPreserved R = true → S.clobber R = false →
    c.σ.regs.get? R = S.ghost g R
  memOut : ∀ a : Nat, ¬ S.foot g a → c.σ.mem[a]? = (S.mem0 g)[a]?
  side : S.postSide g res c

/-- The exit predicate with the result witness bound (the Triple's post; the
one sanctioned existential — consumers `obtain ⟨res, hexit⟩` and then use
`ExitP`'s named fields). -/
def ExitPost (S : CallSpec G Res) (g : G) : Config → Prop :=
  fun c => ∃ res : Res, S.ExitP g res c

/-- **The Triple-shaped meaning** of a `CallSpec` at one ghost pack. -/
def holds (S : CallSpec G Res) (g : G) : Prop :=
  Triple (fun c => S.EntryP g c) (S.ExitPost g)

/-- **`Sat`** — the spec is satisfied (by its real theorem) at EVERY ghost pack.
A pilot instance's `Sat` proof is the thin wrapper tying the record to the
landed contract theorem. -/
def Sat (S : CallSpec G Res) : Prop :=
  ∀ g : G, S.holds g

end CallSpec

/-! ## The canonical `AInv`-stability shape

Every splice so far threaded its own `hAInvStable*` premise (per-window mem
agreement + gp agreement).  `MallocContract.AInv` is an ABSTRACT structure
field, so stability cannot be PROVED once — but it can be NAMED once: this is
the single shape, with the footprint a parameter, plus the monotonicity that
lets one big-footprint premise (e.g. "stable under any change confined to the
caller's stack red zone") serve every smaller-footprint use. -/

/-- The ONE canonical allocator-invariant stability shape: `AInv … exts`
survives any state change that preserves `gp` and touches memory only inside
the footprint `F`. -/
def AInvStableOn (AInv : MState → List (Nat × Nat) → Prop)
    (exts : List (Nat × Nat)) (F : Nat → Prop) : Prop :=
  ∀ σa σb : MState,
    σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
    (∀ a : Nat, ¬ F a → σa.mem[a]? = σb.mem[a]?) →
    AInv σa exts → AInv σb exts

/-- Stability under a BIG footprint transfers to any smaller one. -/
theorem AInvStableOn.mono {AInv : MState → List (Nat × Nat) → Prop}
    {exts : List (Nat × Nat)} {F F' : Nat → Prop}
    (hsub : ∀ a, F' a → F a) (h : AInvStableOn AInv exts F) :
    AInvStableOn AInv exts F' :=
  fun σa σb hgp hmem => h σa σb hgp (fun a ha => hmem a (fun h' => ha (hsub a h')))

#print axioms AInvStableOn.mono

/-! ## Pilot 1: `strlen` — from `strlen_spec_framed`

The leaf reader: no clobber, EMPTY footprint, result ghost-determined
(`Res := Unit`), post pin `x10 = ofNat s.length`, domain post `mem = m0`. -/

/-- The `strlen` ghost pack. -/
structure StrlenG where
  /-- The string pointer (`a0` at entry). -/
  p : BitVec 64
  /-- The string. -/
  s : String
  /-- The entry memory. -/
  m0 : Std.ExtHashMap Nat (BitVec 8)
  /-- The return address. -/
  r : BitVec 64
  /-- The ABI register ghost. -/
  gm : (R : Register) → Option (RegisterType R)
  /-- Return-address alignment (canonicalised into `EntryP.raAligned`). -/
  hr4 : r.toNat % 4 = 0

/-- **`strlen` as a `CallSpec`.** -/
def strlenCallSpec : CallSpec StrlenG Unit where
  entry _ := 0x80006cf0#64
  ret g := g.r
  ghost g := g.gm
  prePins g := [(10, g.p)]
  mem0 g := g.m0
  preSide g c := StrlenLoaded c.σ.mem ∧ StrRegions g.p g.s.length ∧
    g.p.toNat % 8 = 0 ∧ CString g.m0 g.p.toNat g.s
  clobber _ := false
  foot _ _ := False
  postPins g _ := [(10, BitVec.ofNat 64 g.s.length)]
  postSide g _ c := c.σ.mem = g.m0

/-- **`strlen_spec_framed` inhabits `strlenCallSpec`** (thin wrapper; the landed
theorem untouched). -/
theorem strlenCallSpec_sat : strlenCallSpec.Sat := by
  intro g c hE
  obtain ⟨hloaded, hregions, hp8, hcstr⟩ := hE.side
  have ha0 : c.σ.regs.get? Register.x10 = some g.p := hE.args.1
  have hpre : strlen_pre g.p g.r g.s g.m0 c :=
    ⟨hE.good, hloaded, hE.mem, hE.pc, ha0, hE.ra, hE.good.minstret, hE.tick,
     hregions, hp8, hcstr, hE.raAligned⟩
  obtain ⟨c', hsteps, hpost, hgh', htick'⟩ :=
    strlen_spec_framed g.p g.r g.s g.m0 g.gm c ⟨hpre, hE.abi⟩
  obtain ⟨hG', hpc', hx10', _hra', hmem'⟩ := hpost
  refine ⟨c', hsteps, (), hG', htick', hpc', ⟨hx10', trivial⟩,
    fun R hR _ => hgh' R hR,
    fun a _ => show c'.σ.mem[a]? = g.m0[a]? by rw [hmem'], hmem'⟩

#print axioms strlenCallSpec_sat

/-! ## Pilot 2: `malloc` — from `MallocContract.spec`

The interface callee: no clobber, footprint = `privFoot ∪ stack-window`,
`Res := Nat` with `0` encoding NULL (`postSide` carries the disjunction). -/

/-- The `malloc` ghost pack (over a fixed contract's `maxReq`). -/
structure MallocG (maxReq : Nat) where
  /-- The request size. -/
  n : Nat
  /-- Bounded request (feeds `M.spec`'s side condition). -/
  hn : n ≤ maxReq
  /-- The live-extent ledger. -/
  exts : List (Nat × Nat)
  /-- The entry stack pointer. -/
  sp : BitVec 64
  /-- The entry memory. -/
  m0 : Std.ExtHashMap Nat (BitVec 8)
  /-- The return address. -/
  r : BitVec 64
  /-- The ABI register ghost. -/
  gm : (R : Register) → Option (RegisterType R)
  /-- Return-address alignment. -/
  hr4 : r.toNat % 4 = 0

variable {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}

/-- **`malloc` as a `CallSpec`** (over a `MallocContract`). -/
def mallocCallSpec (M : MallocContract A SL gpv headroom maxReq) :
    CallSpec (MallocG maxReq) Nat where
  entry _ := BitVec.ofNat 64 mallocEntry
  ret g := g.r
  ghost g := g.gm
  prePins g := [(10, BitVec.ofNat 64 g.n), (2, g.sp), (3, gpv)]
  mem0 g := g.m0
  preSide g c := StackOK SL g.sp headroom ∧ M.AInv c.σ g.exts
  clobber _ := false
  foot g a := M.privFoot a ∨ (SL.lo ≤ a ∧ a < g.sp.toNat)
  postPins g res := [(10, BitVec.ofNat 64 res), (2, g.sp), (3, gpv)]
  postSide g res c :=
    (res = 0 ∧ M.AInv c.σ g.exts) ∨
    (res ≠ 0 ∧ res % 16 = 0 ∧ A.contains res g.n ∧
      (∀ e ∈ g.exts, ExtDisjoint (res, g.n) e) ∧
      M.AInv c.σ ((res, g.n) :: g.exts))

/-- **`MallocContract.spec` inhabits `mallocCallSpec M`** (thin wrapper). -/
theorem mallocCallSpec_sat (M : MallocContract A SL gpv headroom maxReq) :
    (mallocCallSpec M).Sat := by
  intro g c hE
  obtain ⟨hstackOK, hainv⟩ := hE.side
  obtain ⟨ha0, hsp, hgp, -⟩ := hE.args
  obtain ⟨c', hsteps, hpost⟩ :=
    M.spec g.gm g.exts g.n g.sp g.r g.m0 g.hn c
      ⟨hE.good, hE.tick, hE.pc, ha0, hE.ra, hE.raAligned, hsp, hstackOK, hgp,
       hE.abi, hainv, hE.mem⟩
  obtain ⟨hG', htick', hpc', hsp', hgp', habi', hdisj, hout⟩ := hpost
  -- result witness: 0 on the NULL branch, the fresh pointer otherwise.
  have hcommon : ∀ res : Nat,
      c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 res) →
      ((res = 0 ∧ M.AInv c'.σ g.exts) ∨
       (res ≠ 0 ∧ res % 16 = 0 ∧ A.contains res g.n ∧
        (∀ e ∈ g.exts, ExtDisjoint (res, g.n) e) ∧
        M.AInv c'.σ ((res, g.n) :: g.exts))) →
      (mallocCallSpec M).ExitPost g c' := by
    intro res hx10 hside
    exact ⟨res, hG', htick', hpc', ⟨hx10, hsp', hgp', trivial⟩,
      fun R hR _ => habi' R hR,
      fun a ha => hout a (fun h => ha (Or.inl h)) (fun h => ha (Or.inr h)),
      hside⟩
  rcases hdisj with ⟨hx10, hainv'⟩ | ⟨p, hx10, hpne, hp16, hcont, hdis, hainv'⟩
  · exact ⟨c', hsteps, hcommon 0 hx10 (Or.inl ⟨rfl, hainv'⟩)⟩
  · exact ⟨c', hsteps,
      hcommon p hx10 (Or.inr ⟨hpne, hp16, hcont, hdis, hainv'⟩)⟩

#print axioms mallocCallSpec_sat

/-! ## Pilot 3: `memcpy` (byte route) — from `memcpy_spec_framed_byte`

No clobber, footprint = `[dst, dst+n)`, `Res` = the exit register ghost `g'`
(the byte path's `NotWrittenB` frame is keyed to a fresh ghost), domain post =
the landed `memcpy_bytepath_post` itself. -/

/-- The `memcpy` (byte-route) ghost pack. -/
structure MemcpyByteG where
  /-- Destination pointer. -/
  dst : BitVec 64
  /-- Source pointer. -/
  src : BitVec 64
  /-- Byte count. -/
  n : Nat
  /-- The copied-byte oracle. -/
  bs : Nat → BitVec 8
  /-- The entry memory. -/
  m0 : Std.ExtHashMap Nat (BitVec 8)
  /-- The return address. -/
  r : BitVec 64
  /-- The ABI register ghost. -/
  gm : (R : Register) → Option (RegisterType R)
  /-- Return-address alignment. -/
  hr4 : r.toNat % 4 = 0
  /-- The byte-route condition (misaligned xor, or a small copy). -/
  hroute : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ n < 8

/-- **`memcpy` (byte route) as a `CallSpec`.** -/
def memcpyByteCallSpec :
    CallSpec MemcpyByteG ((R : Register) → Option (RegisterType R)) where
  entry _ := 0x80006bc8#64
  ret g := g.r
  ghost g := g.gm
  prePins g := [(10, g.dst), (11, g.src), (12, BitVec.ofNat 64 g.n)]
  mem0 g := g.m0
  preSide g c := MemcpyLoaded c.σ.mem ∧ Regions g.dst g.src g.n ∧ 0 < g.n ∧
    MemInv g.dst g.src g.n g.bs 0 g.m0 c.σ.mem ∧
    (∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g.gm R)
  clobber _ := false
  foot g a := g.dst.toNat ≤ a ∧ a < g.dst.toNat + g.n
  postPins g _ := [(10, g.dst)]
  postSide g res c := memcpy_bytepath_post res g.r g.dst g.n g.m0 g.bs c

/-- **`memcpy_spec_framed_byte` inhabits `memcpyByteCallSpec`** (thin wrapper). -/
theorem memcpyByteCallSpec_sat : memcpyByteCallSpec.Sat := by
  intro g c hE
  obtain ⟨hloaded, hregions, hnpos, hmeminv, hframe⟩ := hE.side
  obtain ⟨ha0, ha1, ha2, -⟩ := hE.args
  have hPre : PreDispatch g.gm g.r g.dst g.src g.n g.m0 g.bs c :=
    { good := hE.good, loaded := hloaded, pc := hE.pc, a0 := ha0, a1 := ha1,
      a2 := ha2, ra := hE.ra, minstret := hE.good.minstret, tick := hE.tick,
      regions := hregions, npos := hnpos, meminv := hmeminv, hframe := hframe }
  obtain ⟨c', hsteps, hpost, hgh'⟩ :=
    memcpy_spec_framed_byte g.gm g.r g.dst g.src g.n g.m0 g.bs
      hE.raAligned g.hroute c ⟨hPre, hE.abi⟩
  obtain ⟨g', hbp⟩ := hpost
  obtain ⟨hG', hpc', hx10', hra', hcopied, houtside, htick', hframe'⟩ := hbp
  refine ⟨c', hsteps, g', hG', htick', hpc', ⟨hx10', trivial⟩,
    fun R hR _ => hgh' R hR,
    fun a ha => houtside a (by
      have ha' : ¬ (g.dst.toNat ≤ a ∧ a < g.dst.toNat + g.n) := ha
      omega), ?_⟩
  exact ⟨hG', hpc', hx10', hra', hcopied, houtside, htick', hframe'⟩

#print axioms memcpyByteCallSpec_sat

end Vsa.Sim

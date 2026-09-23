import VsaIris.Interp.Store
import VsaIris.Vsa.AllocHoles
import VsaIris.CallAbort

/-!
# `env_*` helper specifications (INTERP_DESIGN.md §9, package H1)

The statements only (MachCSL `Spec<F>`: callers take a spec as a hypothesis,
never a proof import, `claude-notes/spec-modules.md`). The proofs are
`ProofEnvNew.lean`, `ProofEnvGet.lean`, `ProofEnvSet.lean`,
`ProofEnvDefine.lean`.

Every spec is mode-generic (`∀ Wp : MachWP`) and is stated over R's
predicates: the one store `storeRepr`, the persistent `frameAt`/`strAt`, the
value slots `valAt`/`slot24`, and the allocator's `heapRes` in either regime
(`heapStore`, the heap-and-store part of `world`).

* `env_get`/`env_set` never allocate and always return: `fnSpecW`.
* `env_new`/`env_define` allocate. In the counted regime (total mode) they
  cannot fail, and consume exactly the cost model's charge
  (`envBytes`, `defineCost`). In the uncounted regime `malloc`/`realloc` may
  return NULL and the helper takes its out-of-memory arm: `fnSpecAbort`, whose
  abort resource `oomAt …` is the arm's state before its `fwrite` (H5 runs it
  to `exit(1)`). The abort resource carries `⌜ρ = .uncounted⌝`, so a total
  caller discharges the abort branch by that pure fact.

Callee specs taken as hypotheses (proved by other lanes): `strcmpSpec`,
`strlenSpec`, `memcpySpec` (H3), the allocator (`VsaHeap.AllocHoles`, H4) and
`realloc(NULL, n)` (`ReallocNullRuns`, an `IrisHoles` field, H4).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

theorem htifLo_eq : htifLo = Vsa.Sim.tohostAddr := rfl

/-! ## Entries, registers, stack -/

def envNewPC : BitVec 64 := 0x800029fc#64
def envDefinePC : BitVec 64 := 0x80002a5c#64
def envGetPC : BitVec 64 := 0x80002c10#64
def envSetPC : BitVec 64 := 0x80002cdc#64
def strcmpPC : BitVec 64 := 0x80006ea0#64
def strlenPC : BitVec 64 := 0x80006cf0#64
def memcpyPC : BitVec 64 := 0x80006bc8#64

/-- The caller-saved registers other than `ra`, `a0`, `a1`, `a2`
(`t0-t2`, `a3-a7`, `t3-t6`). With `a1`, `a2` this is `vsaClob`. -/
def argClob : List Nat := [5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- Every caller-saved register but `ra`/`a0`: what a helper hands back
clobbered. -/
def retClob : List Nat := 11 :: 12 :: argClob

/-- The callee-saved registers each helper preserves: `s0-s6`, the file a
span owns (`VsaIris.Sym.eRegs`). `env_new` spills `s0` (and `malloc` below it
`s0-s3`); `env_get`/`env_set` spill `s0-s5`; `env_define` spills `s0-s6`. -/
def newSaved : List Nat := [8, 9, 18, 19, 20, 21, 22]
def getSaved : List Nat := [8, 9, 18, 19, 20, 21, 22]
def defineSaved : List Nat := [8, 9, 18, 19, 20, 21, 22]

/-- Stack each helper uses below its entry `sp`: its own frame, plus the
allocator's `allocHeadroom` for the two that call it. `strcmp`, `strlen` and
`memcpy` are leaves. -/
def envNewNeed : Nat := 16 + allocHeadroom
def envGetNeed : Nat := 64
def envDefineNeed : Nat := 64 + allocHeadroom

/-- The caller's `sp` at a helper entry: 16-aligned, in 32-bit RAM, with
`need` bytes above the HTIF words. -/
structure EnvSp (s : BitVec 64) (need : Nat) : Prop where
  lo : htifLo + 16 + need ≤ s.toNat
  hi : s.toNat ≤ 0x100000000
  align : s.toNat % 16 = 0

/-- A 24-byte value slot the helpers load or store: RAM above HTIF, 8-aligned. -/
structure SlotWin (a : Nat) : Prop where
  lo : 0x80000000 ≤ a
  hi : a + 24 ≤ 0x100000000
  htif : htifLo + 16 ≤ a
  align : a % 8 = 0

/-- A byte range a copy reads or writes: RAM, off the HTIF words. -/
structure RamWin (a n : Nat) : Prop where
  lo : 0x80000000 ≤ a
  hi : a + n ≤ 0x100000000
  htif : a + n ≤ htifLo ∨ htifLo + 16 ≤ a

/-! ## The heap and the store -/

/-- Credits added to a regime: `c` more in the counted one, none in the
uncounted one (which has no credits). -/
def Regime.plus : Regime → Nat → Regime
  | .counted k, c => .counted (k + c)
  | .uncounted, _ => .uncounted

@[simp] theorem Regime.plus_counted (k c : Nat) : (Regime.counted k).plus c = .counted (k + c) :=
  rfl
@[simp] theorem Regime.plus_uncounted (c : Nat) : Regime.uncounted.plus c = .uncounted := rfl

section Store

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **The heap and the store**, the part of `world` the allocating helpers
change (at the binary's heap shape `vsaLayoutP` and credits `vsaRoomB`). -/
def heapStore (N : NativeAddrs) (ρ : Regime) (s : Store) : IProp GF :=
  iprop(∃ H B, heapRes vsaLayoutP vsaRoomB ρ H ∗ storeRepr N s B ∗ ⌜∀ b ∈ B, b ∈ H⌝)

/-- `world` is the heap and store beside the console and the context. -/
theorem world_heapStore (N : NativeAddrs) (inp : Nat) (ρ : Regime) (st : St) (d : Nat) :
    world (GF := GF) N vsaLayoutP vsaRoomB inp ρ st d ⊣⊢
      heapStore N ρ st.store ∗ consoleOwn st.out ∗ interpCtx inp d := by
  unfold world heapStore
  constructor
  · iintro ⟨%H, %B, Hh, Hs, Hc, Hi, %hB⟩
    iframe Hc Hi
    iexists H, B
    iframe Hh Hs
    ipureintro; exact hB
  · iintro ⟨⟨%H, %B, Hh, Hs, %hB⟩, Hc, Hi⟩
    iexists H, B
    iframe Hh Hs Hc Hi
    ipureintro; exact hB

/-- What `env_get` leaves in its `out` slot and `a0`: the value found through
the parent chain (`Store.get?`), or nothing and `0`. -/
def getOut (N : NativeAddrs) (s : Store) (fa : Addr) (x : String) (out res : BitVec 64) :
    IProp GF :=
  match s.get? fa x with
  | some v => iprop(⌜res = 1#64⌝ ∗ valAt N out.toNat v)
  | none => iprop(⌜res = 0#64⌝ ∗ slot24 out.toNat)

/-- The store `env_set` leaves: `Store.set?`'s, or the old one when `x` is
unbound on the chain (then `a0 = 0` and C's caller raises the error). -/
def setOut (N : NativeAddrs) (s : Store) (B : List (Nat × Nat)) (fa : Addr) (x : String)
    (v : Value) (res : BitVec 64) : IProp GF :=
  match s.set? fa x v with
  | some s' => iprop(⌜res = 1#64⌝ ∗ storeRepr N s' B)
  | none => iprop(⌜res = 0#64⌝ ∗ storeRepr N s B)

/-- **The out-of-memory arm of an allocating helper**, parked at `pc`: the
setup of `fwrite("out of memory\n", 1, 14, stderr)` before `exit(1)`
(`env.c`'s `xmalloc`, `0x80002a38`, and `env_define`'s array check,
`0x80002bd0`). H5 runs it to `exit(1)` (with `newlib.fprintf`). The helper
hands over its registers at unknown values, the stack it was given with `sp`
inside it, and the (uncounted) heap. The store is dropped: after a partial
growth (`names` reallocated, `vals` not) no frame representation holds, and
`exit(1)` never reads it. -/
def oomAt (pc sp0 s : BitVec 64) (need : Nat) (regs : List Nat) : IProp GF :=
  iprop(PC ↦ᵣ pc ∗ sp ↦ᵣ sp0 ∗ clobbered regs ∗ stackScratch s need ∗
    ∃ H, heapRes vsaLayoutP vsaRoomB .uncounted H)

/-! ## Callee specs (hypotheses; H3 proves them) -/

variable {M : MachineModel}

/-- `strcmp(p, q)`: `a0` is zero exactly when the strings are equal. The
strings are persistent; their `StrWin` covers the word over-read. -/
def strcmpSpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (p q : BitVec 64) (x y : String), fnSpecW Wp strcmpPC
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ p ∗ (11 : Nat) ↦ᵣ q ∗
      clobbered (12 :: argClob) ∗ strAt p.toNat x ∗ strAt q.toNat y))
    (fun _ => iprop(∃ res : BitVec 64, (10 : Nat) ↦ᵣ res ∗ ⌜res = 0#64 ↔ x = y⌝ ∗
      clobbered retClob)))

/-- `strlen(p)`. -/
def strlenSpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (p : BitVec 64) (x : String), fnSpecW Wp strlenPC
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ p ∗ clobbered retClob ∗ strAt p.toNat x))
    (fun _ => iprop((10 : Nat) ↦ᵣ BitVec.ofNat 64 x.length ∗ clobbered retClob)))

/-- `memcpy(dst, src, n)` from read-only bytes into an owned block. -/
def memcpySpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (dst src : BitVec 64) (n : Nat) (img : Nat → BitVec 8), fnSpecW Wp memcpyPC
    (fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin dst.toNat n ∧ RamWin src.toNat n⌝ ∗
      (10 : Nat) ↦ᵣ dst ∗ (11 : Nat) ↦ᵣ src ∗ (12 : Nat) ↦ᵣ BitVec.ofNat 64 n ∗
      clobbered argClob ∗ blockOwn dst.toNat n ∗ roImg (InExt (src.toNat, n)) img))
    (fun _ => iprop((10 : Nat) ↦ᵣ dst ∗ clobbered retClob ∗
      ownImg (InExt (dst.toNat, n)) (fun a => img (a - dst.toNat + src.toNat)))))

instance (Wp : MachWP (GF := GF) M) : Persistent (strcmpSpec Wp) := by
  unfold strcmpSpec; infer_instance
instance (Wp : MachWP (GF := GF) M) : Persistent (strlenSpec Wp) := by
  unfold strlenSpec; infer_instance
instance (Wp : MachWP (GF := GF) M) : Persistent (memcpySpec Wp) := by
  unfold memcpySpec; infer_instance

/-! ## The helper specs -/

/-- **`env_new(par)`** (`env.c:12`): a fresh empty frame under `po`, whose
`Env*` is `par` (`parentAt`). It charges `envBytes` credits. -/
def envNewSpec (Wp : MachWP (GF := GF) M) (N : NativeAddrs) : IProp GF :=
  iprop(□ ∀ (ρ : Regime) (st : Store) (po : Option Addr) (par s : BitVec 64)
      (saved : List (Nat × BitVec 64)), ⌜saved.map Prod.fst = newSaved⌝ →
    fnSpecAbort Wp envNewPC
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp s envNewNeed⌝ ∗ (10 : Nat) ↦ᵣ par ∗ sp ↦ᵣ s ∗
        gp ↦ᵣ□ gpV ∗ clobbered retClob ∗ savedOwn saved ∗ stackScratch s envNewNeed ∗
        parentAt po par.toNat ∗ heapStore N (ρ.plus envBytes) st))
      (fun _ => iprop(∃ e : BitVec 64, (10 : Nat) ↦ᵣ e ∗ sp ↦ᵣ s ∗ clobbered retClob ∗
        savedOwn saved ∗ stackScratch s envNewNeed ∗ heapStore N ρ (st.allocFrame po).1 ∗
        frameAt st.frames.size e.toNat))
      (iprop(⌜ρ = .uncounted⌝ ∗ oomAt 0x80002a38#64 (s - 16#64) s envNewNeed
        (VsaIris.ra :: 10 :: retClob ++ newSaved))))

/-- **`env_get(env, name, out)`** (`env.c:43`): `Store.get?` through the
parent chain, copying the found value into `out`. -/
def envGetSpec (Wp : MachWP (GF := GF) M) (N : NativeAddrs) : IProp GF :=
  iprop(□ ∀ (st : Store) (B : List (Nat × Nat)) (fa : Addr) (x : String) (e pn out s : BitVec 64)
      (saved : List (Nat × BitVec 64)), ⌜saved.map Prod.fst = getSaved⌝ →
    fnSpecW Wp envGetPC
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp s envGetNeed ∧ SlotWin out.toNat⌝ ∗
        (10 : Nat) ↦ᵣ e ∗ (11 : Nat) ↦ᵣ pn ∗ (12 : Nat) ↦ᵣ out ∗ sp ↦ᵣ s ∗
        clobbered argClob ∗ savedOwn saved ∗ stackScratch s envGetNeed ∗ frameAt fa e.toNat ∗
        strAt pn.toNat x ∗ slot24 out.toNat ∗ storeRepr N st B))
      (fun _ => iprop(∃ res : BitVec 64, (10 : Nat) ↦ᵣ res ∗ sp ↦ᵣ s ∗ clobbered retClob ∗
        savedOwn saved ∗ stackScratch s envGetNeed ∗ storeRepr N st B ∗
        getOut N st fa x out res)))

/-- **`env_set(env, name, v)`** (`env.c:56`): `Store.set?` through the
parent chain; `v` is passed by reference (`a2` points at the caller's copy). -/
def envSetSpec (Wp : MachWP (GF := GF) M) (N : NativeAddrs) : IProp GF :=
  iprop(□ ∀ (st : Store) (B : List (Nat × Nat)) (fa : Addr) (x : String) (v : Value)
      (e pn pv s : BitVec 64) (saved : List (Nat × BitVec 64)), ⌜saved.map Prod.fst = getSaved⌝ →
    fnSpecW Wp envSetPC
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp s envGetNeed ∧ SlotWin pv.toNat⌝ ∗
        (10 : Nat) ↦ᵣ e ∗ (11 : Nat) ↦ᵣ pn ∗ (12 : Nat) ↦ᵣ pv ∗ sp ↦ᵣ s ∗
        clobbered argClob ∗ savedOwn saved ∗ stackScratch s envGetNeed ∗ frameAt fa e.toNat ∗
        strAt pn.toNat x ∗ valAt N pv.toNat v ∗ storeRepr N st B))
      (fun _ => iprop(∃ res : BitVec 64, (10 : Nat) ↦ᵣ res ∗ sp ↦ᵣ s ∗ clobbered retClob ∗
        savedOwn saved ∗ stackScratch s envGetNeed ∗ valAt N pv.toNat v ∗
        setOut N st B fa x v res)))

/-- **`env_define(env, name, v)`** (`env.c:22`): `Store.define`, charging
`defineCost` (name copy, and array growth on a canonical cap). -/
def envDefineSpec (Wp : MachWP (GF := GF) M) (N : NativeAddrs) : IProp GF :=
  iprop(□ ∀ (ρ : Regime) (st : Store) (fa : Addr) (x : String) (v : Value)
      (e pn pv s : BitVec 64) (saved : List (Nat × BitVec 64)),
      ⌜saved.map Prod.fst = defineSaved⌝ →
    fnSpecAbort Wp envDefinePC
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp s envDefineNeed ∧ SlotWin pv.toNat⌝ ∗
        (10 : Nat) ↦ᵣ e ∗ (11 : Nat) ↦ᵣ pn ∗ (12 : Nat) ↦ᵣ pv ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpV ∗
        clobbered argClob ∗ savedOwn saved ∗ stackScratch s envDefineNeed ∗ frameAt fa e.toNat ∗
        strAt pn.toNat x ∗ valAt N pv.toNat v ∗ heapStore N (ρ.plus (defineCost st fa x)) st))
      (fun _ => iprop(sp ↦ᵣ s ∗ clobbered (10 :: retClob) ∗ savedOwn saved ∗
        stackScratch s envDefineNeed ∗ valAt N pv.toNat v ∗ heapStore N ρ (st.define fa x v)))
      (iprop(⌜ρ = .uncounted⌝ ∗ oomAt 0x80002bd0#64 (s - 64#64) s envDefineNeed
        (VsaIris.ra :: 10 :: retClob ++ defineSaved) ∗ valAt N pv.toNat v)))

end Store

/-! ## `realloc(NULL, n)` (an `IrisHoles` field)

`env_define`'s first growth calls `realloc(NULL, 64)` and `realloc(NULL, 192)`
(`names`/`vals` are NULL while `cap = 0`). `_realloc_r` tail-calls
`_malloc_r` on a NULL pointer (`0x80005290: beqz a1`, `0x80005484: j
_malloc_r`), so the run is `malloc`'s from `realloc`'s entry with the
request in `a1`. `AllocHoles` covers only the grow path of a live block;
these two runs are stated like `MallocChgRun`/`MallocLocalRun` and H4
discharges them with seven step lemmas (`st_8000527c` …) and its
`_malloc_r` entry lemma. -/

/-- The register values at a `realloc(NULL, n)` entry. -/
structure ReallocNullRegs (rv : Nat → BitVec 64) (r n s : BitVec 64)
    (saved : List (Nat × BitVec 64)) : Prop where
  entry : EntryRegs rv reallocEntryBV r 0#64 s saved
  a1 : rv a1 = n

/-- Counted `realloc(NULL, n)`. -/
def ReallocNullChgRun (M : MachineModel) : Prop :=
  ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (k c : Nat),
    saved.map Prod.fst = vsaSaved → vsaChg n.toNat c → SpOKA s → r.toNat % 4 = 0 →
    ReallocNullRegs rv r n s saved →
    vsaLayoutP.Shape mv H → vsaRoomB mv H (k + c) →
    (∀ a, stackWin s allocHeadroom a → ¬ heapFoot vsaLayoutP H a) →
    ∃ fuel, LocalRun M [(gp, gpV)] allocText (allocRegs vsaClob vsaSaved)
      (mallocBytes vsaLayoutP H s allocHeadroom)
      (MallocRoomEnd vsaLayoutP vsaRoomB H n r s saved k) fuel rv mv

/-- Uncounted `realloc(NULL, n)`: NULL with the heap unchanged, or a fresh block. -/
def ReallocNullLocalRun (M : MachineModel) : Prop :=
  ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8),
    saved.map Prod.fst = vsaSaved → SpOKA s → r.toNat % 4 = 0 →
    ReallocNullRegs rv r n s saved →
    vsaLayoutP.Shape mv H → (∀ a, stackWin s allocHeadroom a → ¬ heapFoot vsaLayoutP H a) →
    ∃ fuel, LocalRun M [(gp, gpV)] allocText (allocRegs vsaClob vsaSaved)
      (mallocBytes vsaLayoutP H s allocHeadroom) (MallocEnd vsaLayoutP H n r s saved) fuel rv mv

/-- **`realloc(NULL, n)` at the binary** (`IrisHoles.reallocNull`). -/
structure ReallocNullHoles : Prop where
  /-- Counted: a charged request returns a fresh block. -/
  chgRun : ∀ live, AllocLive live → ReallocNullChgRun (vsaModel live)
  /-- Uncounted: NULL with the heap unchanged, or a fresh block. -/
  localRun : ∀ live, AllocLive live → ReallocNullLocalRun (vsaModel live)

end VsaIris.Interp

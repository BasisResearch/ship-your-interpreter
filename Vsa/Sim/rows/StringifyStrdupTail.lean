import Vsa.Sim.rows.StringifySpec
import Vsa.Sim.EnvDefCompose

-- discipline: allow(R7-conj-tower-def) The only NEW post here is `StrdupTailExit`
-- (one `∃ res`), consumed exclusively through its named destructurer
-- `StrdupTailExit.freshCString` (defined immediately below it — R7-compliant). The
-- remaining `∃` occurrences the raw line-grep counts are (a) doc-comment prose and
-- (b) the malloc/memcpy callee-contract POST shapes (`∃ p, …`, `∃ g', …`) inlined
-- VERBATIM from `EnvDefCompose`'s already-grandfathered `envDef*Splice` bridge
-- types — the canonical LANDED contract interfaces, not new anonymous towers.

/-!
# `StringifyStrdupTail` — the shared `strdup` tail `0x80003044` composed (Shape-D)

Task #64 gap (2).  The `stringify` (`Value.display`) callee at `0x80002fc0`
funnels EVERY non-str branch (int/bool/null — and the str branch's own copy) into
ONE shared tail at `0x80003044`:

```
80003044  mv   a0,s1                            -- a0 = buf   (the NUL-terminated scratch)
80003048  jal  strlen@80006cf0                  -- a0 = len(buf)
8000304c  addi a2,a0,1 ; mv a0,a2 ; sd a2,8(sp) -- a2 = len+1  (spilled)
80003058  jal  malloc@80004790                  -- malloc(len+1) → a0
8000305c  ld   a2,8(sp) ; mv s0,a0 ; beqz a0 -> 80003140  -- OOM guard (arena: no-OOM)
80003068  mv   a1,s1 ; jal memcpy@80006bc8      -- memcpy(new, buf, len+1)  (copies the NUL)
80003070  ld   ra ; mv a0,s0 ; ld s0/s1 ; addi sp,sp,112 ; ret   -- return the fresh copy
```

This is EXACTLY the append-path splice of `env_define` (`Vsa/Sim/EnvDefCompose.lean`:
`envDefAppendContract` = `strlen ≫ malloc ≫ memcpy ≫ store`) with the final store
block replaced by the return epilogue `mv a0,s0 ; ret` — the three callees are the
SAME framed contracts (`strlen_spec_framed`, `MallocContract.spec`,
`memcpy_spec_framed_byte`).  We therefore reuse `EnvDefCompose`'s frame-carrying
splices VERBATIM as callees and land the composed tail here.

The per-block MACHINE BRIDGES (`mv`/`addi`/`beqz` arg staging, the `mv a0,s0 ; ret`
epilogue) are named Shape-A hypotheses — the honest remaining straight-line work,
each a `#derive_case`/`chain_facts` segment over pinned bytes — but the CALL
COMPOSITION (the hard Shape-D algebra) and the CString-preservation reasoning are
proved here and are axiom-clean.

The concluding fact is `StringifyStrdupTailResid` (`StringifySpec.lean:222`): given
a NUL-terminated `CString m buf str`, the tail returns a fresh non-null pointer
`res` holding `CString m' res str`.  The memcpy post copies `len+1` bytes — the
whole C-string INCLUDING the terminating NUL — so `CString m' res str` follows
byte-for-byte from `CString m buf str`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.While (Value)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc

namespace Vsa.Sim

/-! ## The reseated frame ghost — `gm[x8 := dst]`

The strdup tail's `mv s0,a0` (`0x80003060`) RESEATS the callee-saved `s0`/x8 from the
malloc-staging value (`old`) to the malloc result `dst` (deliberate: s0 carries `new`
across the memcpy call for the epilogue's `mv a0,s0`).  The malloc frame is threaded
under the entry ghost `gm` (s0 = gm x8 = old); the memcpy frame must therefore be
threaded under the RESEATED ghost `gm[x8 := dst]`.  `AbiPreserved x8 = true`, so
`EnvDefFrame.hAbi` genuinely pins s0 — a single `gm` cannot honour both entries
(machine-checked in `strdupMemcpy_frame_obstruction`, `StrdupTailContractClose.lean`).
This is the amendment the ledger's `strdup-memcpy-s0-reseat-frameghost` entry proposed. -/

/-- **The reseated frame ghost** `gm[x8 := dst]`: agrees with `gm` off `x8`, maps `x8`
to the malloc result `dst`.  `RegisterType Register.x8 = BitVec 64` (by `rfl`), so the
dependent update `h ▸ dst` is well-typed. -/
def ghostReseatS0 (gm : (R : Register) → Option (RegisterType R)) (dst : BitVec 64) :
    (R : Register) → Option (RegisterType R) :=
  fun R => if h : R = Register.x8 then some (h ▸ dst) else gm R

@[simp] theorem ghostReseatS0_x8 (gm : (R : Register) → Option (RegisterType R))
    (dst : BitVec 64) : ghostReseatS0 gm dst Register.x8 = some dst := by
  simp [ghostReseatS0]

theorem ghostReseatS0_ne (gm : (R : Register) → Option (RegisterType R)) (dst : BitVec 64)
    {R : Register} (h : R ≠ Register.x8) : ghostReseatS0 gm dst R = gm R := by
  simp [ghostReseatS0, h]

/-! ## The tail's exit predicate — a fresh `CString` in `a0`

The strdup tail returns (in `a0`) a fresh, non-null heap pointer whose C-string is
the copied string `str`.  We name this the tail's honest exit surface, keyed to the
result string (the buffer's contents), parameterised like the other framed callee
posts (`res` in `x10`, memory `m'`). -/

/-- The `strdup`-tail exit: at PC = the return target `r`, `x10 = res` is a
non-null pointer whose memory holds `CString m' res str`.  This is the surface the
`stringify` branches expose to the concat cell (each returns a fresh printed
buffer). -/
def StrdupTailExit (r : BitVec 64) (str : String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  ∃ res : Nat, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 res) ∧
    res ≠ 0 ∧ CString c.σ.mem res str

/-- **Named destructurer** for `StrdupTailExit` (per CLAUDE.md R7: consume a landed
∃/∧ tower through ONE named lemma, never `.2.2.2` positional chains).  Reads the
fresh-result witness `(res, m')` out of the tail exit: a non-null pointer holding
`CString m' res str`.  This is the single reader the resid producers below (gap 1 +
gap 2) and the concat cell (gap 3) all share — the exponentiating collapse of the
three identical "run the Triple, read off res/m'" hand-destructurings into one. -/
theorem StrdupTailExit.freshCString {r : BitVec 64} {str : String} {c : Config}
    (h : StrdupTailExit r str c) : ∃ res : Nat, res ≠ 0 ∧ CString c.σ.mem res str :=
  ⟨h.2.2.choose, h.2.2.choose_spec.2.1, h.2.2.choose_spec.2.2⟩

/-! ## The composed tail contract — `strlen ≫ malloc ≫ memcpy ≫ epilogue`

Mirrors `envDefAppendContract` exactly.  The three callees are the framed
contracts; the four inter-block machine bridges (`bridgeStrlenPre` = the `mv a0,s1`
prefix landing `strlen_pre`; `bridgeMallocPre` = `addi a2,a0,1 ; mv a0,a2 ; sd` +
malloc-pre marshalling; `bridgeMemcpyPre` = the OOM-guard + `mv a1,s1` staging; and
the epilogue `bridgeEpilogue` = `ld ra ; mv a0,s0 ; ret`, which reads back the
fresh block's `CString` from the memcpy post's copied bytes) are named Shape-A
hypotheses.  The composition is pure `callSeg` algebra over the real callees. -/

/-- **The composed `strdup`-tail contract.**  From a caller-supplied tail-entry
predicate `P` (the branch-specific setup landing `s1 = buf`, `CString m buf str`),
through `strlen ≫ malloc ≫ memcpy ≫ epilogue` — each callee a framed contract, each
seam a named machine bridge — the tail reaches `StrdupTailExit rRet str` (a fresh
`CString` in `a0`).  Structurally identical to `envDefAppendContract`, epilogue in
place of the store block. -/
theorem stringifyStrdupTailContract
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {P : Config → Prop}
    (M : MallocContract A SL gpv headroom maxReq)
    (gm : (R : Register) → Option (RegisterType R))
    (str : String) (rRet : BitVec 64)
    -- strlen call data
    (bufPtr rStrlen : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    -- malloc call data
    (exts : List (Nat × Nat)) (nMalloc : Nat) (spM rM : BitVec 64)
    (mMalloc : Std.ExtHashMap Nat (BitVec 8)) (hnM : nMalloc ≤ maxReq)
    -- memcpy call data (dispatch ghost = the ABI ghost `gm`; byte route)
    (rMemcpy dst src : BitVec 64) (nMemcpy : Nat)
    (mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halignC : rMemcpy.toNat % 4 = 0)
    (extsC : List (Nat × Nat)) (spC : BitVec 64)
    (hrouteCbyte : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ nMemcpy < 8)
    (hAInvStableFootC : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < dst.toNat ∨ dst.toNat + nMemcpy ≤ a) → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa extsC → M.AInv σb extsC)
    -- strlen preserves the carried frame (its missing preservation clause, named)
    (strlenFramed : Triple
      (fun c => strlen_pre bufPtr rStrlen str m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c)
      (fun c => strlen_post rStrlen str m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c))
    -- the four machine bridges
    (bridgeStrlenPre : Triple P
      (fun c => strlen_pre bufPtr rStrlen str m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c))
    (bridgeMallocPre : Triple
      (fun c => strlen_post rStrlen str m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 nMalloc) ∧
        c.σ.regs.get? Register.x1 = some rM ∧ rM.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some spM ∧ StackOK SL spM headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        M.AInv c.σ exts ∧ c.σ.mem = mMalloc))
    (bridgeMemcpyPre : Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some rM ∧
        c.σ.regs.get? Register.x2 = some spM ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ exts) ∨
         (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
           p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p nMalloc ∧
           (∀ e ∈ exts, ExtDisjoint (p, nMalloc) e) ∧
           M.AInv c.σ ((p, nMalloc) :: exts))) ∧
        (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < spM.toNat) →
          c.σ.mem[a]? = mMalloc[a]?))
      (fun c => PreDispatch (ghostReseatS0 gm dst) rMemcpy dst src nMemcpy mMemcpy bs c ∧
        EnvDefFrame SL gpv headroom M.AInv extsC spC (ghostReseatS0 gm dst) c))
    -- the return epilogue: reads back the fresh block's CString from the copied
    -- bytes (memcpy copied `len+1` bytes incl. NUL → `CString m' dst str`), lands
    -- `mv a0,s0 ; ret` at `rRet`.  The frame is threaded under the RESEATED ghost
    -- `gm[x8 := dst]` (the `mv s0,a0` reseated s0 to `dst`; see `ghostReseatS0`).
    (bridgeEpilogue : Triple
      (fun c => (∃ g', memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs c) ∧
        EnvDefFrame SL gpv headroom M.AInv extsC spC (ghostReseatS0 gm dst) c)
      (StrdupTailExit rRet str)) :
    Triple P (StrdupTailExit rRet str) :=
  -- strlen ≫ [malloc ≫ [memcpy(framed) ≫ epilogue]]
  envDefStrlenSplice bufPtr rStrlen str m0 strlenFramed bridgeStrlenPre
    (envDefMallocSplice M gm exts nMalloc spM rM mMalloc hnM bridgeMallocPre
      (envDefMemcpyFramedSplice (ghostReseatS0 gm dst) rMemcpy dst src nMemcpy mMemcpy bs
        (envDefMemcpyFramed SL gpv headroom M.AInv extsC spC (ghostReseatS0 gm dst)
          rMemcpy dst src nMemcpy mMemcpy bs halignC hrouteCbyte hAInvStableFootC)
        bridgeMemcpyPre bridgeEpilogue))

/-! ## Discharging `StringifyStrdupTailResid` from the composed contract

`StringifyStrdupTailResid` (`StringifySpec.lean`) is the abstract, memory-generic
surface: `∀ m buf str, CString m buf str → ∃ res m', res ≠ 0 ∧ CString m' res str`.
It is exactly `stringifyStrdupTailContract`'s conclusion read off at any concrete
tail-entry configuration — the machine Triple witnesses the existential.  The
remaining premise is `EntrySupplied`: for each `(m, buf, str)` there is a config
`c` satisfying the tail-entry predicate `P` (the branch landed the buffer at
`s1 = buf`, `c.σ.mem = m`, `CString m buf str`).  This is what the `stringify`
per-kind branches provide (str = `ld a1,8(a0)` + `sd`; int = the snprintf buffer;
bool/null = the literal store) — named, not assumed away. -/

/-- **`StringifyStrdupTailResid` discharged** from a composed-tail contract plus an
entry-configuration supplier.  Given, for every `(m, buf, str)` with
`CString m buf str`, a tail Triple `Triple (P m buf str) (StrdupTailExit r str)`
and a witnessing entry config satisfying `P m buf str`, the abstract residual
holds: run the Triple, read `res`/`m'` off `StrdupTailExit`. -/
theorem stringifyStrdupTailResid_of_contract
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (P : Std.ExtHashMap Nat (BitVec 8) → Nat → String → Config → Prop)
    (r : Std.ExtHashMap Nat (BitVec 8) → Nat → String → BitVec 64)
    (tail : ∀ (m : Std.ExtHashMap Nat (BitVec 8)) (buf : Nat) (str : String),
      CString m buf str → Triple (P m buf str) (StrdupTailExit (r m buf str) str))
    (entry : ∀ (m : Std.ExtHashMap Nat (BitVec 8)) (buf : Nat) (str : String),
      CString m buf str → ∃ c, P m buf str c) :
    StringifyStrdupTailResid g N A SL := by
  intro m buf str hcs
  obtain ⟨c, hPc⟩ := entry m buf str hcs
  obtain ⟨c', _hsteps, hexit⟩ := tail m buf str hcs c hPc
  obtain ⟨res, hne, hcs'⟩ := hexit.freshCString
  exact ⟨res, c'.σ.mem, hne, hcs'⟩

/-! ## Gap (1): `StringifyContract` produced from the whole-call composition

`StringifyContract` (`StringifySpec.lean`) is the callee post at the
`Value.display` level: `∀ sp r, ∃ res m', StringifyResult m' store res v` — i.e.
`res ≠ 0 ∧ CString m' res (v.display store)`.  The WHOLE `stringify` call is
`dispatch@0x80002fc0 ≫ per-kind branch ≫ strdup-tail@0x80003044`: the 5-way kind
ladder selects a branch, each branch lands a NUL-terminated buffer at `s1` holding
`v.display store` (str: the payload directly; int: `snprintf %lld`; bool/null:
literal store), then the shared strdup tail (`stringifyStrdupTailContract`,
`StrdupTailExit r (v.display store)`) returns the fresh copy.

Since `StrdupTailExit r str`'s existential body IS `StringifyResult`'s body at
`str = v.display store` (both = `res ≠ 0 ∧ CString m' res str` in `a0`), the whole
call is: land the tail-entry (dispatch ≫ branch, an entry-config supplier), run the
tail Triple, read off the result.  This factors `StringifyContract` through the
strdup tail + a dispatch/branch entry supplier — no `display` residue beyond what
each branch's buffer already realises. -/

/-- **`StringifyContract` produced** from the whole-call composition.  Given, for
each `(sp, r)`, a whole-`stringify`-call Triple to `StrdupTailExit rRet
(v.display store)` (the dispatch ≫ branch ≫ strdup-tail composition of
`stringifyStrdupTailContract`) and a witnessing entry configuration (the caller
landing `ValueRepr v` at `aVal`, `mem = m0`), `StringifyContract` holds: run the
Triple, read `res`/`m'` off the fresh-`CString` exit.  This is the honest surface
of the assembled `stringify` call — the abstract residual `StringifyContract`
witnessed by the machine composition. -/
theorem stringifyContract_of_call
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Vsa.While.Addr → Nat)
    (store : Vsa.While.Store) (aVal : Nat) (v : Value) (m0 : Mem)
    (rRet : BitVec 64) (Pentry : BitVec 64 → BitVec 64 → Config → Prop)
    (call : ∀ (sp r : BitVec 64),
      Triple (Pentry sp r) (StrdupTailExit rRet (v.catDisplay store)))
    (entry : ∀ (sp r : BitVec 64), ∃ c, Pentry sp r c) :
    StringifyContract g N A SL φf φc store aVal v m0 := by
  intro sp r
  obtain ⟨c, hPc⟩ := entry sp r
  obtain ⟨c', _hsteps, hexit⟩ := call sp r c hPc
  -- `StringifyResult`'s body = `StrdupTailExit`'s fresh-CString witness at
  -- `str = v.display store`; read it off through the ONE named destructurer.
  obtain ⟨res, hne, hcs'⟩ := hexit.freshCString
  exact ⟨res, c'.σ.mem, hne, hcs'⟩

#print axioms ghostReseatS0
#print axioms ghostReseatS0_x8
#print axioms ghostReseatS0_ne
#print axioms StrdupTailExit
#print axioms stringifyStrdupTailContract
#print axioms stringifyStrdupTailResid_of_contract
#print axioms stringifyContract_of_call

end Vsa.Sim

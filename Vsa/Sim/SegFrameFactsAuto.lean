import Vsa.Sim.SegFrameFacts
import Vsa.Sim.BlockAdapter
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.EqNeDispatchSeg
import Vsa.Sim.DivDispatchSeg
import Vsa.Sim.DeriveCaseRow

/-!
# `seg_frame_facts` — discharge a whole seg's `ChainFacts` bundle from ONE `FrameBundle`

`chain_facts h with "<prefix>"` (`ChainFactsTac`) strips every decode/byte-pin leaf
of a `#derive_case` segment, leaving exactly the frame-geometry residual: one
`MemFacts` per `ld`/`sd` plus the seg's data-dependent branch guards.  This file
closes all of it uniformly:

* `frameBundle_writeLog` — a `FrameBundle` survives the chain's threaded stores
  (`pop` survives `writeLog`), so a later block's loads read their (still populated)
  threaded memory with the SAME bundle.
* `frame_ld_read` / `frame_sd_auto` — the per-window leaves, offset read off `a.imm`,
  everything else `decide`/`rfl` from the bundle.  `frame_ld_read`'s byte list is the
  EXPLICIT frame read `[popByte m fb.pop (base+off), …]` — a function of `base`/`off`
  only, never of the pin list `L`, so the tactic fills the seg's `lds` element with no
  occurs-check and no `L` reduction (the key to keeping the assembled proof cheap).
  `frame_sd_auto` is bounds-only (works over any threaded memory).
* `seg_frame_facts h with "<prefix>" using fb` — the tactic.  It provisions the
  existential `lds` (fresh element metavariables the load leaves fill), runs
  `chain_facts`, peels the identity `stepMemM` layers off each `MemFacts`, then closes
  every frame window from `fb` (with `frameBundle_writeLog` carrying `fb` onto a
  later block's threaded memory) and every concrete kind guard by `decide`.  The seg's
  genuine semantic guards (e.g. `Wr ≠ 0` for `div`) are left as residual goals.

Together with `chain_facts` this reduces a binary-op arm's `SegPre` construction to
one `FrameBundle` + the arm's genuine guard, replacing the ~200-line per-row
`spill_addr`/`read64_bytes`/`writeMap8`-disjoint ritual.  Landed and axiom-clean on
`eqDispatch_facts` (the whole `eq` arm, one block, ~2s) and — since the cross-block fix
below — on `divDispatch_facts` (the whole `div` arm, FOUR blocks with loads spanning
stores), both composed into live `Triple`s (`eqDispatchRow_frame`/`divDispatchRow_frame`).

CROSS-BLOCK (the `div` frontier, now closed): when a *later* block's load reads memory
the *earlier* blocks stored to (div's D2 loads under D1's `sd`s), the block-entry memory
is `writeLog σ.mem (wlogM D1 … lds)`.  Two things had to stay `writeLog`/`runGM`-fold-free
so the kernel never reduces the threaded tower:
* the READ — `frame_ld_read_thru` reads those bytes from the UNDERLYING `σ.mem` and
  discharges the threaded-memory pins by store/load-window DISJOINTNESS
  (`writeLog_getElem_disjoint`, `wlogM_below`, offsets `+0x90..+0xa0` vs `+0xf0/+0x100`);
* the ASSEMBLY — every per-leaf `hsrc`/guard `srcVal` peels the `runGM` tower with
  `srcVal_runGM_ne` (`srcval_peel`, Fix 1a), NOT `by rfl`; and the leaf-memory
  normalisation peels the identity `stepMemM` layers with an explicit chained-`rfl`
  equation (`sffPeelMemEq`), NOT `g.change`'s `isDefEq` (which whnf'd the `writeLog` fold
  on the third cross-block load — the actual blowup).
Every arm — single-block (eq/ne) OR cross-block (div, and mod/eq/ne / recursive M4 arms
whose loads span stores) — is now closed by the uniform tactic; see Acceptance 2.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

/-! ## `pop` survives the chain's threaded stores -/

/-- The frame-memory populated predicate (the `FrameBundle.pop` field). -/
def Populated (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ k : Nat, ∃ w : BitVec 8, m[k]? = some w

/-- `pop` survives one hashmap `insert`. -/
theorem pop_insert {m : Std.ExtHashMap Nat (BitVec 8)} (a : Nat) (v : BitVec 8)
    (hpop : Populated m) : Populated (m.insert a v) := by
  intro k
  rw [Std.ExtHashMap.getElem?_insert]
  split
  · exact ⟨v, rfl⟩
  · exact hpop k

/-- `pop` survives one write-log entry (`applyW`): every width is a tower of
`insert`s, and the catch-all leaves `m` unchanged. -/
theorem pop_applyW (m : Std.ExtHashMap Nat (BitVec 8)) (e : WEntry)
    (hpop : Populated m) : Populated (applyW m e) := by
  obtain ⟨a, w, d⟩ := e
  unfold applyW
  split
  · exact pop_insert _ _ hpop
  · unfold writeMap4
    exact pop_insert _ _ (pop_insert _ _ (pop_insert _ _ (pop_insert _ _ hpop)))
  · unfold writeMap8
    exact pop_insert _ _ (pop_insert _ _ (pop_insert _ _ (pop_insert _ _
      (pop_insert _ _ (pop_insert _ _ (pop_insert _ _ (pop_insert _ _ hpop)))))))
  · exact hpop

/-- `pop` survives a whole write-log fold. -/
theorem pop_writeLog (log : List WEntry) (m : Std.ExtHashMap Nat (BitVec 8))
    (hpop : Populated m) : Populated (writeLog m log) := by
  induction log generalizing m with
  | nil => exact hpop
  | cons e rest ih =>
    have hstep : writeLog m (e :: rest) = writeLog (applyW m e) rest := by
      simp only [writeLog, List.foldl_cons]
    rw [hstep]
    exact ih (applyW m e) (pop_applyW m e hpop)

/-- A `FrameBundle` propagates across a write-log fold: the geometry (`lo`/`hi`/
`htif`/`al`, all about `base`) is unchanged and `pop` survives (`pop_writeLog`). -/
theorem frameBundle_writeLog {m : Std.ExtHashMap Nat (BitVec 8)} {base : BitVec 64}
    (log : List WEntry) (fb : FrameBundle m base) : FrameBundle (writeLog m log) base where
  pop := pop_writeLog log m fb.pop
  lo := fb.lo
  hi := fb.hi
  htif := fb.htif
  al := fb.al

/-! ## The per-window leaves (offset read off `a.imm`) -/

/-- A `ld` window `MemFacts` from a `FrameBundle` over the load's own memory, with
the offset read off `a.imm`; the tactic supplies `hk`/`hsrc`/`hoff`/`hoff8` by
`decide`/`rfl`.  Returns the read bytes for the caller's `lds`. -/
theorem frame_ld_auto (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (base : BitVec 64) (fb : FrameBundle m base) (hk : a.kind = .ld)
    (hsrc : srcVal a.rs1 L = base)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ 0x108)
    (hoff8 : (sign_extend (m := 64) a.imm : BitVec 64).toNat % 8 = 0) :
    ∃ bs : List (BitVec 8), MemFacts m L bs a :=
  frame_ld m L a base ((sign_extend (m := 64) a.imm : BitVec 64).toNat) fb hk hsrc rfl hoff hoff8

/-! ### Loads via an explicit (`L`-independent) read window

`frame_ld_auto` returns the read bytes inside an `∃`; closing a threaded load goal
with its `Exists.choose` makes the assigned byte list mention the goal's pin list
`L` (through the choice term), and `L` itself threads those same byte
metavariables — a spurious occurs-check that would force reducing the whole `L`.
Instead read the window explicitly with `popByte` (choice on a single `pop` fact):
the resulting byte list depends only on `base`/`off`, never on `L`, so the leaf
assigns `?bᵢ := window` with no occurs-check and no `L` reduction. -/

/-- The (choice-picked) byte the populated memory holds at `k`. -/
noncomputable def popByte (m : Std.ExtHashMap Nat (BitVec 8))
    (h : ∀ k : Nat, ∃ w : BitVec 8, m[k]? = some w) (k : Nat) : BitVec 8 :=
  (h k).choose

theorem popByte_spec (m : Std.ExtHashMap Nat (BitVec 8))
    (h : ∀ k : Nat, ∃ w : BitVec 8, m[k]? = some w) (k : Nat) :
    m[k]? = some (popByte m h k) := (h k).choose_spec

/-- A `ld` window `MemFacts` whose byte list is the EXPLICIT frame read
`[popByte m fb.pop (base+off), … , +7]` — a function of `base`/`off` only, never of
`L`.  The offset is read off `a.imm`; the tactic supplies `hk`/`hsrc`/`hoff`/`hoff8`
by `decide`/`rfl`. -/
theorem frame_ld_read (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (base : BitVec 64) (fb : FrameBundle m base) (hk : a.kind = .ld)
    (hsrc : srcVal a.rs1 L = base)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ 0x108)
    (hoff8 : (sign_extend (m := 64) a.imm : BitVec 64).toNat % 8 = 0) :
    MemFacts m L
      (let o := base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat
       [popByte m fb.pop o, popByte m fb.pop (o + 1), popByte m fb.pop (o + 2),
        popByte m fb.pop (o + 3), popByte m fb.pop (o + 4), popByte m fb.pop (o + 5),
        popByte m fb.pop (o + 6), popByte m fb.pop (o + 7)]) a := by
  have hea : (eaddrM a L).toNat
      = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat :=
    frame_ea a L base _ hsrc rfl (by omega) fb
  refine memFacts_ld_frame m L a _ _ _ _ _ _ _ _ hk
    (by rw [hea]; have := fb.lo; omega) (by rw [hea]; have := fb.hi; omega)
    (by rw [hea]; have := fb.htif; right; omega) (by rw [hea]; have := fb.al; omega)
    (by rw [hea]; exact popByte_spec _ _ _) (by rw [hea]; exact popByte_spec _ _ _)
    (by rw [hea]; exact popByte_spec _ _ _) (by rw [hea]; exact popByte_spec _ _ _)
    (by rw [hea]; exact popByte_spec _ _ _) (by rw [hea]; exact popByte_spec _ _ _)
    (by rw [hea]; exact popByte_spec _ _ _) (by rw [hea]; exact popByte_spec _ _ _)

/-- Every write-log entry a block body emits has width `1`/`4`/`8` — a `wlogM` entry
is a `wentryM` of a `sb`/`sw`/`sd`, whose width is `widthOfM` of that kind.  Discharges
`frame_ld_read_thru`'s `hw` for ANY seg, no reduction. -/
theorem wlogM_widths : ∀ (body : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
    (e : WEntry), e ∈ wlogM body L lds → e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 8 := by
  intro body
  induction body with
  | nil => intro L lds e he; simp only [wlogM, List.not_mem_nil] at he
  | cons a rest ih =>
    intro L lds e he
    rw [wlogM] at he
    -- the entry's width, when `a` is a store, is `widthOfM a.kind ∈ {1,4,8}`.
    cases hk : a.kind <;> rw [hk] at he <;>
      first
        | exact ih _ _ e he
        | (rcases List.mem_cons.mp he with rfl | he
           · rw [show (wentryM a L).2.1 = widthOfM a.kind from rfl, hk]; decide
           · exact ih _ _ e he)

/-- `lookupG` ignores a key erased at a different index. -/
theorem lookupG_eraseG_ne (n rd : Nat) (h : n ≠ rd) :
    ∀ L : GRegs, lookupG n (eraseG rd L) = lookupG n L := by
  intro L
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [eraseG]
    split
    · next hkrd => rw [ih, lookupG, if_neg (by omega)]
    · next hkrd => rw [lookupG, lookupG, ih]

/-- A source read is unchanged by a `stepGM` that writes a different register — so a
frame base pinned in `x2` survives the whole block (no instruction writes `x2`). -/
theorem srcVal_stepGM_ne (a : MInstr) (L : GRegs) (bs : List (BitVec 8)) (n : Nat)
    (h : n ≠ a.rd) : srcVal n (stepGM a L bs) = srcVal n L := by
  unfold stepGM
  cases n with
  | zero => split <;> rfl
  | succ m =>
    split <;>
      first
        | rfl
        | (show (lookupG (m+1) ((a.rd, wvalM a L bs) :: eraseG a.rd L)).getD 0#64
              = (lookupG (m+1) L).getD 0#64
           rw [lookupG, if_neg (by omega), lookupG_eraseG_ne (m+1) a.rd (by omega) L])

/-- **The whole-block source-preservation lemma** (Fix 1a).  A source read of `x n`
survives the ENTIRE block's pin-list fold `runGM body L lds`, provided no element of
the body writes `x n` (`decide`-able on the concrete body).  Proved by induction with
each step `srcVal_stepGM_ne` — it NEVER reduces the `runGM` fold, so a use site
discharges `srcVal n (runGM body L lds) = srcVal n L` in `O(1)` structural work instead
of the `O(#instructions)` deep `rfl` the threaded tower would otherwise force. -/
theorem srcVal_runGM_ne (n : Nat) : ∀ (body : List MInstr),
    (∀ a ∈ body, a.rd ≠ n) → ∀ (L : GRegs) (lds : List (List (BitVec 8))),
      srcVal n (runGM body L lds) = srcVal n L := by
  intro body
  induction body with
  | nil => intro _ L lds; rfl
  | cons a rest ih =>
    intro h L lds
    rw [runGM, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    exact srcVal_stepGM_ne a L (lds.headD []) n (h a (List.mem_cons_self ..)).symm

/-- **Abstract the read over `wlogM`.**  Every write-log entry of a block body whose
frame stores use `x2 = base` (preserved: no instruction writes `x2`) has address
`base.toNat + off` for that store's own offset `off ≤ 0x108`.  Proven ONCE by
induction (reducing `wlogM`); at a use site it lets a caller bound the store addresses
WITHOUT reducing `wlogM` — so `wlogM`/`writeLog` can be sealed for the block-threading
kernel check. -/
theorem wlogM_store_offsets :
    ∀ (body : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
      (base : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (fb : FrameBundle m base),
      srcVal 2 L = base →
      (∀ a ∈ body, a.rd ≠ 2) →
      (∀ a ∈ body, (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb) →
        a.rs1 = 2 ∧ (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0x108) →
      ∀ e ∈ wlogM body L lds,
        ∃ a, a ∈ body ∧ (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb) ∧
          e.1 = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat := by
  intro body
  induction body with
  | nil => intro L lds base m fb _ _ _ e he; simp only [wlogM, List.not_mem_nil] at he
  | cons a rest ih =>
    intro L lds base m fb h2 hrd hst e he
    rw [wlogM] at he
    cases hk : a.kind <;> rw [hk] at he <;> dsimp only [] at he <;> (try rw [← hk] at he) <;>
      first
        | (rcases List.mem_cons.mp he with rfl | he
           · obtain ⟨hrs1, hoff⟩ := hst a (List.mem_cons_self ..) (by rw [hk]; decide)
             refine ⟨a, List.mem_cons_self .., by rw [hk]; decide, ?_⟩
             show (eaddrM a L).toNat = _
             rw [frame_ea a L base _ (by rw [hrs1]; exact h2) rfl hoff fb]
           · obtain ⟨a', ha', hk', he'⟩ :=
               ih L lds base m fb h2 (fun x hx => hrd x (List.mem_cons_of_mem _ hx))
                 (fun x hx => hst x (List.mem_cons_of_mem _ hx)) e he
             exact ⟨a', List.mem_cons_of_mem _ ha', hk', he'⟩)
        | (obtain ⟨a', ha', hk', he'⟩ :=
            ih (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) base m fb
              (by rw [srcVal_stepGM_ne a L (lds.headD []) 2 (hrd a (List.mem_cons_self ..)).symm]
                  exact h2)
              (fun x hx => hrd x (List.mem_cons_of_mem _ hx))
              (fun x hx => hst x (List.mem_cons_of_mem _ hx)) e he
           exact ⟨a', List.mem_cons_of_mem _ ha', hk', he'⟩)

/-- The store-window disjointness `frame_ld_read_thru` needs, DERIVED from
`wlogM_store_offsets` — so it never reduces `wlogM`: every store lies at
`base + off_st` with `off_st ≥ off + 8` (the `hgap`, `decide`-able on the concrete
body), hence entirely above the load window `[base+off, base+off+8)`. -/
theorem wlogM_below (body : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
    (base : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (fb : FrameBundle m base) (off : Nat)
    (h2 : srcVal 2 L = base)
    (hrd : ∀ a ∈ body, a.rd ≠ 2)
    (hst : ∀ a ∈ body, (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb) →
      a.rs1 = 2 ∧ (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0x108)
    (hgap : ∀ a ∈ body, (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb) →
      off + 8 ≤ (sign_extend (m := 64) a.imm : BitVec 64).toNat) :
    ∀ e ∈ wlogM body L lds, base.toNat + off + 8 ≤ e.1 := by
  intro e he
  obtain ⟨a, ha, hk, haddr⟩ := wlogM_store_offsets body L lds base m fb h2 hrd hst e he
  rw [haddr]; have := hgap a ha hk; omega

/-- `frame_ea` as a conditional rewrite: `(eaddrM a L).toNat = base.toNat + off`
(`off = (sext a.imm).toNat`), with the frame side-conditions as auto-params.  Used to
reduce a store log's addresses to `base.toNat + off_st` when proving disjointness. -/
theorem frame_ea_rw {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs}
    {base : BitVec 64} (fb : FrameBundle m base)
    (hsrc : srcVal a.rs1 L = base := by rfl)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0x108 := by decide) :
    (eaddrM a L).toNat = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat :=
  frame_ea a L base _ hsrc rfl hoff fb

/-! ### Loads over a threaded (`writeLog`) memory, read from the UNDERLYING memory

A *cross-block* load (div's D2 loads under D1's `sd`s) reads memory the earlier
blocks stored to, so its block-entry memory is `writeLog m0 log`.  Reading it with
`frameBundle_writeLog` makes the byte term carry `log` (which itself mentions the
seg's `lds`) — threaded across the remaining blocks, the assembled proof blows up.
`frame_ld_read_thru` instead reads the bytes from the UNDERLYING `m0` (writeLog-free
terms) and shows the threaded window agrees with `m0` by store/load-window
DISJOINTNESS: the store windows all lie ABOVE the load window (`hbelow`), so
`writeLog_getElem_disjoint` collapses each threaded pin back to `m0`. -/
theorem frame_ld_read_thru (m0 : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry)
    (L : GRegs) (a : MInstr) (base : BitVec 64) (fb : FrameBundle m0 base) (hk : a.kind = .ld)
    (hsrc : srcVal a.rs1 L = base)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ 0x108)
    (hoff8 : (sign_extend (m := 64) a.imm : BitVec 64).toNat % 8 = 0)
    (hw : ∀ e ∈ log, e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 8)
    (hbelow : ∀ e ∈ log,
      base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ e.1) :
    MemFacts (writeLog m0 log) L
      (let o := base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat
       [popByte m0 fb.pop o, popByte m0 fb.pop (o + 1), popByte m0 fb.pop (o + 2),
        popByte m0 fb.pop (o + 3), popByte m0 fb.pop (o + 4), popByte m0 fb.pop (o + 5),
        popByte m0 fb.pop (o + 6), popByte m0 fb.pop (o + 7)]) a := by
  have hea : (eaddrM a L).toNat
      = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat :=
    frame_ea a L base _ hsrc rfl (by omega) fb
  -- every load-window byte agrees with the underlying `m0` (disjoint from all stores)
  have thru : ∀ j : Nat, j < 8 →
      (writeLog m0 log)[base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat + j]?
        = m0[base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat + j]? := by
    intro j hj
    exact writeLog_getElem_disjoint _ log m0 hw
      (fun e he => Or.inl (by have := hbelow e he; omega))
  refine memFacts_ld_frame (writeLog m0 log) L a _ _ _ _ _ _ _ _ hk
    (by rw [hea]; have := fb.lo; omega) (by rw [hea]; have := fb.hi; omega)
    (by rw [hea]; have := fb.htif; right; omega) (by rw [hea]; have := fb.al; omega)
    (by rw [hea]; exact (thru 0 (by omega)).trans (popByte_spec _ _ _))
    (by rw [hea]; exact (thru 1 (by omega)).trans (popByte_spec _ _ _))
    (by rw [hea]; exact (thru 2 (by omega)).trans (popByte_spec _ _ _))
    (by rw [hea]; exact (thru 3 (by omega)).trans (popByte_spec _ _ _))
    (by rw [hea]; exact (thru 4 (by omega)).trans (popByte_spec _ _ _))
    (by rw [hea]; exact (thru 5 (by omega)).trans (popByte_spec _ _ _))
    (by rw [hea]; exact (thru 6 (by omega)).trans (popByte_spec _ _ _))
    (by rw [hea]; exact (thru 7 (by omega)).trans (popByte_spec _ _ _))

/-- A `sd` window `MemFacts` — bounds only, so it holds over ANY memory `m`; only
the frame `base`'s geometry (`fb`, over `base_mem`) is consumed. -/
theorem frame_sd_auto (m base_mem : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (base : BitVec 64) (bs : List (BitVec 8)) (fb : FrameBundle base_mem base)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = base)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ 0x108)
    (hoff8 : (sign_extend (m := 64) a.imm : BitVec 64).toNat % 8 = 0) :
    MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat
      = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat :=
    frame_ea a L base _ hsrc rfl (by omega) fb
  refine memFacts_sd_frame m L a bs hk ?_ ?_ ?_ ?_
  · rw [hea]; have := fb.lo; omega
  · rw [hea]; have := fb.hi; omega
  · rw [hea]; have := fb.htif; omega
  · rw [hea]; have := fb.al; omega

/-! ## The tactic -/

open Lean Elab Tactic Meta

/-- Build a proof of `srcVal n L = base` by peeling the `runGM` fold layer-by-layer
with `srcVal_runGM_ne` (each layer's `∀ a ∈ body, a.rd ≠ n` by `decide`) — never
reducing the fold — bottoming out at the entry pins with `rfl` (`defeq`, over the
shallow entry `L` only).  This replaces the per-leaf `by rfl` `hsrc`/`h2`, whose
`rfl` reduced the whole threaded tower (the Fix-1a lever). -/
private partial def srcvalPeelProof (goalTy : Expr) : MetaM Expr := do
  let some (_, lhs, _rhs) := goalTy.eq? | throwError "srcval_peel: goal is not an Eq"
  match lhs.getAppFnArgs with
  | (``srcVal, #[nE, lE]) =>
      match lE.getAppFnArgs with
      | (``runGM, #[bodyE, lE', ldsE]) =>
          -- `srcVal_runGM_ne n body : (∀ a ∈ body, a.rd ≠ n) → ∀ L lds, …`
          let f ← mkAppOptM ``srcVal_runGM_ne #[some nE, some bodyE]
          let premTy := (← inferType f).bindingDomain!
          let prem ← mkDecideProof premTy
          -- `lem : srcVal n (runGM body L' lds) = srcVal n L'`
          let lem ← mkAppM' (← mkAppM' f #[prem]) #[lE', ldsE]
          -- recurse on `srcVal n L' = base`
          let innerLhs := mkApp2 (mkConst ``srcVal) nE lE'
          let innerTy ← mkEq innerLhs _rhs
          let innerPf ← srcvalPeelProof innerTy
          mkEqTrans lem innerPf
      | _ => mkEqRefl lhs   -- entry pins: `srcVal n L = base` by `rfl` (shallow `L`)
  | _ => mkEqRefl lhs

/-- `srcval_peel` closes a `srcVal n L = base` goal by peeling the `runGM` tower with
`srcVal_runGM_ne` (Fix 1a) — `O(1)` structural work per layer, no fold reduction. -/
elab "srcval_peel" : tactic => do
  let g ← getMainGoal
  let pf ← g.withContext (srcvalPeelProof (← instantiateMVars (← g.getType)))
  g.assign pf

/-- Peel the identity `stepMemM` layers off a memory expression, returning the peeled
memory `m'` together with a proof `m = m'`.  Each `stepMemM m0 a L = m0` layer is a
ONE-STEP match reduction (`a.kind` is a concrete non-store), proved by a `rfl` typed at
exactly that layer — so the proof NEVER whnf's the underlying `writeLog`/`runGM` fold
(the `isDefEq`-driven blowup that `g.change` fell into on a 3-deep cross-block load). -/
private partial def sffPeelMemEq (m : Expr) : MetaM (Expr × Expr) := do
  match m.getAppFnArgs with
  | (``stepMemM, #[m0, a, _]) =>
      -- peel ONLY an identity (non-store) layer.  Decide by decoding `a.kind` ALONE
      -- (bounded) — NEVER `whnf m` (that would reduce the underlying `writeLog` fold).
      -- A store layer is `applyW m0 …` ≠ `m0`; stop there (the closer handles the
      -- store-wrapped memory directly via `frame_sd_auto`, which holds over any `m`).
      let kind ← whnf (← mkAppM ``MInstr.kind #[a])
      let isStore := match kind.getAppFn.constName? with
        | some ``MKind.sw | some ``MKind.sd | some ``MKind.sb => true
        | _ => false
      if isStore then
        return (m, ← mkEqRefl m)
      else
        -- `hint : m = m0` (kernel checks `stepMemM m0 a L` reduces to `m0` in one
        -- match step on the concrete `a.kind`, never touching `m0`).
        let hint ← mkExpectedTypeHint (← mkEqRefl m0) (← mkEq m m0)
        let (m', pf0) ← sffPeelMemEq m0
        return (m', ← mkEqTrans hint pf0)
  | _ => return (m, ← mkEqRefl m)

/-- Peel the identity `stepMemM` layers off a `MemFacts m L bs a` goal's memory
(defeq), so `fb`/`frameBundle_writeLog` speak about the block-entry memory
(`σ.mem`/`writeLog σ.mem log`).  The pin list `L` and byte list `bs` are left as-is:
because the frame leaves' data (`frame_ld_read`'s window, `frame_sd_auto`'s `bs`) never
mention `L`, there is no occurs-check and hence no need to reduce `L`. -/
private def sffNormMem (g : MVarId) : TacticM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  match ty.getAppFnArgs with
  | (``MemFacts, #[m, l, bs, a]) =>
      if !(m.isAppOf ``stepMemM) then return g   -- nothing to peel
      let (m', pf) ← sffPeelMemEq m              -- pf : m = m'
      -- lift `pf` to `MemFacts m l bs a = MemFacts m' l bs a` by congruence on the
      -- memory argument, then replace the goal target — no `isDefEq` on the fold.
      let mTy ← inferType m
      let f ← withLocalDeclD `x mTy fun x =>
        mkLambdaFVars #[x] (mkAppN (mkConst ``MemFacts) #[x, l, bs, a])
      let tyEq ← mkAppM ``congrArg #[f, pf]
      let ty' := mkAppN (mkConst ``MemFacts) #[m', l, bs, a]
      try g.replaceTargetEq ty' tyEq catch _ => return g
  | _ => return g

/-- Count the `writeLog` layers at the head of a (peeled) memory expression — the
number of `frameBundle_writeLog` wraps needed to carry `fb` onto it. -/
private partial def sffWriteLogDepth (m : Expr) : Nat :=
  match m.getAppFnArgs with
  | (``writeLog, #[m0, _]) => 1 + sffWriteLogDepth m0
  | _ => 0

/-- Discharge ONE `chain_facts` leftover from the frame bundle `fbE`.  Reads the
leaf's shape (the instruction kind, the memory's `writeLog` nesting) ONCE, then
applies exactly the matching closer — no speculative attempts that each re-reduce
the threaded state.  Returns `true` if closed (frame window or concrete kind guard),
`false` to leave it as a genuine residual (the seg's semantic guard). -/
private def sffCloseLeaf (fbE : Term) (g0 : MVarId) : TacticM Bool := do
  let g ← (do setGoals [g0]; sffNormMem g0)
  let close (t : Syntax) : TacticM Bool := do
    let ok ← observing? (do setGoals [g]; evalTactic t; done)
    return ok.isSome
  let ty ← instantiateMVars (← g.getType)
  match ty.getAppFnArgs with
  | (``MemFacts, #[m, _, _, a]) =>
      let kindE ← g.withContext (whnf (← mkAppM ``MInstr.kind #[a]))
      match kindE.getAppFn.constName? with
      | some ``MKind.ld =>
          match sffWriteLogDepth m with
          | 0 =>
              -- same-memory load: read directly from `fb`.  `hsrc` via `srcval_peel`
              -- (Fix 1a) — never reduces the threaded `runGM` tower.
              close (← `(tactic| refine frame_ld_read _ _ _ _ $fbE ?_ ?_ ?_ ?_ <;>
                first | srcval_peel | rfl | decide))
          | _ =>
              -- cross-block load: read from the UNDERLYING `σ.mem` (`fb`), discharge
              -- the threaded pins by store/load-window disjointness.  `hw` is
              -- `wlogM_widths`; `hbelow` maps the store log to its addresses, rewrites
              -- each by `frame_ea_rw`, and closes by `omega`.
              -- `hbelow` via `wlogM_below` (a proven lemma) — it NEVER reduces `wlogM`,
              -- so `wlogM`/`writeLog` may stay sealed for the block-threading check.
              -- Both `hsrc` (of `frame_ld_read_thru`) and `wlogM_below`'s `h2` go via
              -- `srcval_peel` (Fix 1a), never reducing the `runGM` tower.
              close (← `(tactic|
                refine frame_ld_read_thru _ _ _ _ _ $fbE ?_ ?_ ?_ ?_ (wlogM_widths _ _ _)
                  (wlogM_below _ _ _ _ _ $fbE _ (by srcval_peel) (by decide) (by decide)
                    (by decide)) <;>
                  first | srcval_peel | rfl | decide))
      | some ``MKind.sd =>
          close (← `(tactic| refine frame_sd_auto _ _ _ _ _ _ $fbE ?_ ?_ ?_ ?_ <;>
            first | srcval_peel | rfl | decide))
      | _ => pure false
  | _ =>
      -- a terminator guard `guardB op (srcVal r1 L) (srcVal r2 L) = taken`.  When both
      -- compared registers resolve to concrete values (a `bne` on int-kind tag pins, or
      -- one register set by an in-block `li`), `rfl` reduces the (bounded) `runGM` pin
      -- tower — the `lookupG` short-circuits at the front before any noncomputable
      -- `popByte` load byte — and closes it.  The seg's genuine SEMANTIC guard (e.g. the
      -- divisor `Wr ≠ 0` `beqz`, a symbolic pin) reduces neither way and is left as a
      -- residual goal for the caller.
      close (← `(tactic| first | rfl | decide))

/-- `seg_frame_facts h with "<prefix>" using fb` — on a goal
`∃ lds, ChainFacts m m L lds bs`, provision `lds`, run `chain_facts h with pfx`,
and close every frame window + concrete guard from `fb`, leaving only the seg's
genuine semantic guards as residual goals. -/
elab "seg_frame_facts " h:term " with " pfx:str " using " fbE:term : tactic => do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let ty ← instantiateMVars (← mainGoal.getType)
    -- goal must be `∃ lds, body`
    let some (_, p) := ty.app2? ``Exists | throwError "seg_frame_facts: goal is not an ∃"
    -- the `lds` element type: `List (BitVec 8)`
    let byteTy ← elabTerm (← `(BitVec 8)) none
    let byteListTy ← elabTerm (← `(List (BitVec 8))) none
    let listTy ← elabTerm (← `(List (List (BitVec 8)))) none
    -- provision `lds` as K fresh element metavariables (the load leaves fill them)
    let K := 24
    let mvars ← (List.range K).mapM (fun _ => mkFreshExprMVar byteListTy)
    let elemNilE ← mkAppOptM ``List.nil #[some byteTy]        -- `([] : List (BitVec 8))`
    let nilE ← mkAppOptM ``List.nil #[some byteListTy]        -- `([] : List (List (BitVec 8)))`
    let ldsE ← mvars.foldrM (fun m acc => mkAppM ``List.cons #[m, acc]) nilE
    -- refine ⟨ldsE, ?pf⟩
    let bodyTy := p.beta #[ldsE]
    let pf ← mkFreshExprMVar bodyTy
    mainGoal.assign (← mkAppOptM ``Exists.intro #[some listTy, some p, some ldsE, some pf])
    setGoals [pf.mvarId!]
    -- strip decode/byte-pin leaves
    evalTactic (← `(tactic| chain_facts $h with $pfx))
    -- discharge each remaining leftover
    let leftovers ← getGoals
    let mut residual : List MVarId := []
    for g in leftovers do
      if ← g.isAssigned then continue
      if ← sffCloseLeaf fbE g then pure () else residual := residual ++ [g]
    -- fill any unused `lds` element metavariables
    for mv in mvars do
      let mid := mv.mvarId!
      unless ← mid.isAssigned do mid.assign elemNilE
    setGoals residual

set_option maxRecDepth 100000

/-- **Acceptance 1.**  The whole `eq` arm spill-and-setup block's `ChainFacts`
bundle — six `ld` reloads + six `sd` field spills, no branch guards — discharged
from ONE `FrameBundle σ.mem sp` and the loaded image. -/
theorem eqDispatch_facts (σ : MState) (sp : BitVec 64)
    (fb : FrameBundle σ.mem sp) (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ∃ lds, ChainFacts σ.mem σ.mem (eqDispL sp) lds eqDispatch := by
  seg_frame_facts h with "Vsa.Sim.Code.eval_expr_at_" using fb

#print axioms eqDispatch_facts

/-! ## Acceptance 3 — compose `eqDispatch_facts` into a live `Triple`

`eqDispatchRow` (`EqNeDispatchSeg`) is `Triple (SegPre eqDispatch (eqDispL sp) lds …)
(EqDispatchPost …)`, still parameterised by the seg's `lds`.  `eqDispatch_facts`
supplies the `ChainFacts` conjunct of `SegPre` — so from a config parked at the arm
entry with a `FrameBundle` (instead of a hand-assembled `lds` + `ChainFacts`), we get
a `Triple` whose entry needs only frame geometry.  `SegFramePre` is that
frame-bundle entry predicate; `eqDispatchRow_frame` is the composed row. -/

/-- The frame-bundle arm entry: parked at `pc0` with a `FrameBundle` over the frame
base `sp` (and the loaded code image) in place of a concrete `lds` + its `ChainFacts`
bundle. -/
def SegFramePre (L : GRegs) (sp pc0 : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Vsa.Machine.Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.regs.get? Register.PC = some pc0 ∧
  (∃ vm, c.σ.regs.get? Register.minstret = some vm) ∧
  GHolds c.σ L ∧ KeysOK (keysG L) ∧ FrameBundle m0 sp ∧
  Vsa.Sim.Code.Eval_exprLoaded m0 ∧ c.tick < 2

/-- **The composed `eq` row.**  From the frame-bundle entry `SegFramePre` — no
hand-supplied `lds`/`ChainFacts`, just a `FrameBundle m0 sp` and the loaded image —
the whole `eq` arm spill-and-setup block runs to `EqDispatchPost` for the `lds` the
frame reads.  The `ChainFacts` obligation `eqDispatchRow` carries is discharged by
`eqDispatch_facts`; this is the item-1 SegPre composition. -/
theorem eqDispatchRow_frame (sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegFramePre (eqDispL sp) sp 0x800036e4#64 m0)
      (fun c => ∃ lds, EqDispatchPost sp lds m0 c) := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, hmi, hL, hkeys, fb, hload, htick⟩ := hpre
  -- read the frame's `lds` + its `ChainFacts` from the bundle
  obtain ⟨lds, hfacts⟩ :=
    eqDispatch_facts c.σ sp (hmem ▸ fb) (hmem ▸ hload)
  -- run `eqDispatchRow` at this `lds`
  obtain ⟨c', hstep, hpost⟩ := eqDispatchRow sp lds m0 c
    ⟨hG, hmem, hpc, hmi, hL, hkeys, hfacts, htick⟩
  exact ⟨c', hstep, lds, hpost⟩

#print axioms eqDispatchRow_frame

/-! ## Acceptance 2 — the `div` arm (cross-block): the WHOLE four-block `ChainFacts`,
no seal, no heartbeat bump

The earlier kernel deep-recursion (the four-block `ChainFacts` forced the kernel to
reduce the threaded `writeLog (writeLog σ.mem (wlogM D1 lds)) (wlogM D2 lds)` tower to
match each leaf's type) is KILLED by two structural fixes, both here:

* **`srcval_peel` (`srcVal_runGM_ne`, Fix 1a)** — every leaf's `hsrc`/`h2`
  (`srcVal 2 L = base`) and the divisor guard's `srcVal 17 L = Wr` peel the `runGM` pin
  tower layer-by-layer with the register-preservation lemma, `O(1)` structural work per
  layer, instead of the old `by rfl` that reduced the whole tower per leaf;
* **`sffPeelMemEq` (memory peel by congruence)** — `sffNormMem` no longer `g.change`s
  the leaf memory into the block-entry form via `isDefEq` (which whnf'd the `writeLog`
  fold on the third cross-block load and blew up); it peels the identity `stepMemM`
  layers with an EXPLICIT chained-`rfl` equation (each layer a one-step match reduction
  that never touches `writeLog`) and `replaceTargetEq`.

With those, `divDispatch_facts` assembles the four-block `ChainFacts` in seconds
(axiom-clean, no `maxHeartbeats` slop), leaving exactly ONE residual — the seg's genuine
semantic guard, the divisor-nonzero `beqz` — supplied by the caller as `Wr ≠ 0`.  The
two int-kind `bne` guards close inside the tactic (`rfl` on the bounded pin tower). -/

/-- **Acceptance 2.**  The whole `div` arm dispatch (FOUR blocks, cross-block loads
under earlier stores) as one `ChainFacts` bundle — discharged from ONE `FrameBundle
σ.mem v2`, the loaded image, and the divisor-nonzero fact `Wr ≠ 0`.  No seal, no
heartbeat bump: the kernel never reduces the threaded `writeLog`/`runGM` tower. -/
theorem divDispatch_facts (σ : MState) (v2 sret Wr Wl : BitVec 64) (hWr : Wr ≠ 0)
    (fb : FrameBundle σ.mem v2) (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ∃ lds, ChainFacts σ.mem σ.mem (divDispL v2 sret Wr Wl) lds divDispatch := by
  seg_frame_facts h with "Vsa.Sim.Code.eval_expr_at_" using fb
  -- the only residual is the divisor-nonzero guard `guardB BEQ (srcVal 17 L) 0 = false`
  show guardB bop.BEQ (srcVal 17 _) (srcVal 0 _) = false
  rw [show srcVal 17 _ = Wr from by srcval_peel]
  simp only [guardB]
  exact beq_eq_false_iff_ne.mpr hWr

#print axioms divDispatch_facts

/-- **The composed `div` row.**  From the frame-bundle arm entry `SegFramePre` (a
`FrameBundle m0 v2` + loaded image, no hand-supplied `lds`/`ChainFacts`) plus `Wr ≠ 0`,
the whole `div` arm dispatch runs to `DivDispatchPost` — `divDispatch_facts` supplies
the `ChainFacts` that `divDispatchRow` carries.  The `div` analogue of
`eqDispatchRow_frame`, closing the item-1 `SegPre` composition for the cross-block arm. -/
theorem divDispatchRow_frame (v2 sret Wr Wl : BitVec 64) (hWr : Wr ≠ 0)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegFramePre (divDispL v2 sret Wr Wl) v2 0x800037dc#64 m0)
      (fun c => ∃ lds, DivDispatchPost v2 sret Wr Wl lds m0 c) := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, hmi, hL, hkeys, fb, hload, htick⟩ := hpre
  obtain ⟨lds, hfacts⟩ :=
    divDispatch_facts c.σ v2 sret Wr Wl hWr (hmem ▸ fb) (hmem ▸ hload)
  obtain ⟨c', hstep, hpost⟩ := divDispatchRow v2 sret Wr Wl lds m0 c
    ⟨hG, hmem, hpc, hmi, hL, hkeys, hfacts, htick⟩
  exact ⟨c', hstep, lds, hpost⟩

#print axioms divDispatchRow_frame

end Vsa.Sim

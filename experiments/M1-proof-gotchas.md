# M1 proof gotchas — consolidated from the Layer-0 lemma proofs

Working notes distilled from the proofs in `Vsa/Sim/` (Dispatch, Pmp,
Execute, Hooks, Decode, Tick, MemRead). Read this before writing any new
lemma against the Sail model. The base discipline is E1i's staged simp
(`experiments/E1i_decode_staged.lean`, `experiments/RESULTS.md`): stage-1
`simp only` unfolds the head function, stage-2 one monad-plumbing
`simp_all`, stage-3 small reachable-path passes, stage-4
`BitVec.eq_of_toNat_eq; decide` for width residuals. One-pass simp with
everything times out. Never `rfl`/`whnf`/`decide` on stateful goals.

## Monad plumbing

- SailME.run peel set (fully qualified; do NOT `open PreSail` — it
  shadows `get`/`readReg`): `LeanRV64DExecutable.SailME.run/.throw`,
  `Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run/.throw`,
  `ExceptT.run/.bind/.mk/.lift/.bindCont/.pure`, `liftM, monadLift,
  MonadLift.monadLift, Functor.map, EStateM.map/.run/.bind/.pure`.
- Register reads may appear as both `readReg` and
  `Sail.ConcurrencyInterfaceV1.PreSail.readReg` — the simp set needs
  both, but never pass bare `readReg` as an explicit simp arg when
  ambiguous (resolves to a non-equational def → "Expected a
  proposition"). Rely on `simp_sail` or qualify.
- `for … in [a:b]i` loops live in `ExceptT (Error ⊕ α) (EStateM …)` —
  results are `.ok (.ok …)`. Collapse with the generic
  `Vsa.Sim.forIn'_const`/`forIn'_loop_const` (Pmp.lean), never a
  16-fold unfold. `untilFuelM` loops (checked_mem_read) unfold once when
  split_misaligned gives N=1.
- Reusing a `.run`-form sub-lemma inside a reduced goal: `simp only
  [EStateM.run] at h` first, then `rw`/`exact`.
- `pmpCheck` uses `SailME.throw` as early-return-with-a-VALUE, not as an
  error — reason through it, don't treat throw as the failure path.

## whnf bombs (symptom: elaboration hangs)

- Huge string matches: `csr_name_map_backwards "mip"` (268 arms) — prove
  the UNAPPLIED equation by plain `rfl` (`csr_name_map_backwards "mip" =
  pure 0x344#12`) and rewrite; never feed into `simp [EStateM.run, …]`.
- `currentlyEnabled Ext_X` under `EStateM.bind` — discharge as a
  standalone `.run`-form lemma (misa bit by `decide`) and rewrite the
  applied occurrence.
- Anything touching `runWhileElf`/`whileElf?` symbolically (400k-step
  eval) — `generalize` or `attribute [local irreducible]` first.

## BitVec / decidability

- `Decidable` synthesis fails when widths contain unreduced `Int.toNat`
  — route through `BitVec.eq_of_toNat_eq; decide`.
- `0#64` vs `BitVec.zero 64` vs `zeros (n := 64)`: defeq but not
  syntactic. `BitVec.zero_eq` lands on `0#64`; for `zeros` residuals use
  `have hz : (0#64) = zeros (n := 64) := by apply BitVec.eq_of_toNat_eq;
  decide`.
- `zero_extend (a : BitVec 64)` is NOT syntactically `a`; unfold
  `zero_extend, Sail.BitVec.zeroExtend` then `BitVec.setWidth_eq`. Watch
  `to_bits 4` vs `4#64` mismatches in discriminants — route through a
  `have hmatch : <exact discriminant shape> = _`.
- `physaddrbits = BitVec (if 64 = 32 then 34 else 64)`: defeq to
  `BitVec 64` but omega/bv_omega choke on the symbolic width — reduce to
  width-64 before arithmetic. `Int.tmod (toNatInt a) 4 = 0`-style hyps
  bridge via `Int.ofNat_le.mp/.mpr` + bv_omega.
- Increments come out as `BitVec.addInt x 1` (no normalizer to `+ 1`)
  — downstream statements must expect that form.

## Matches, guards, indices

- 32-way register match on a concrete index: the scrutinee is
  `(Int.ofNat (i#5).toNat).toNat` — reduce with `Sail.BitVec.toNatInt,
  Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat` in ONE
  `simp only`, then iota-reduction picks the arm. Index-agnostic; this
  is the M2 replication pattern.
- Boolean guards `X == X` (InstructionFetch, Machine, Bare) don't close
  by `beq_self_eq_true` — `have := by decide` then `simp only [this]`.
- `Std.ExtDHashMap.get?_insert`'s dite condition is
  `(insertedKey == queriedKey)` — that order. Reading `R` back through
  `insert mtime v` needs `show (mtime == R) = false`.
- Sail indexes vectors with `Int` via a `GetElem? coll Int` instance —
  need both `getElem!_replicate` (Nat) and `getElem!_replicate_int`
  (Pmp.lean).
- `XipReadType.IncludePlatformInterrupts` must be fully qualified or it
  auto-binds as a free variable and the match never reduces.

## State shape

- The model's writes normalize to `{σ with regs := σ.regs.insert …}`
  chains — state RHS states in exactly that spine (StateNF's lemmas
  consume it). Multiline `{σ with …}` literals inside tactic blocks
  break the parser — keep on one line.
- `writeReg` returns PUnit; stating `.ok ()` works, no manual
  `PUnit.unit`.
- Callback/hook no-ops (`xreg_write_callback`, `csr_name_write_callback`
  "mip" path, `fetch_callback`, …): unfold to expose the discarded
  value; never let simp normalize a `reg_name_forwards`-style String.
  Undecidable `if old ≠ new` guards around read-only callbacks: `split`
  and show both arms produce the same state (don't case on the value).
- An `if c then t else e` whose branches are equal collapses without
  deciding `c` — use this for value-dependent guards around no-ops.

## Statement conventions

- Hypotheses: explicit `σ.regs.get? R = some v` per register actually
  read (readReg on a missing key throws). Pin control-plane registers at
  `Vsa/Sim/InitValues.lean` literals; leave machine-mutated registers
  universally quantified. Don't take a whole `GoodState` argument in
  leaf lemmas — the skeleton projects fields.
- Memory hypotheses: `σ.mem[a + k]? = some b` (readByte of unmapped is
  0, no throw — loads don't need totality, but code bytes are pinned).
- Conclusions: `.run σ = .ok v σ'` with σ' syntactically σ (read-only
  paths) or the explicit insert chain in program order.
- The linter flags simp args used only by LATER stages of a multi-step
  pipeline — collapse to single `simp only` calls per goal where
  possible; only then trust "unused" warnings.

## From the fetch proof (Fetch.lean)

- Never `rw` an equation that must traverse a giant monadic term (whnf
  timeout at 8M heartbeats) — prove the leaf fact as a standalone lemma
  and feed its VALUE into the big `simp only`.
- Strict-monad reads are forced even when short-circuited: a
  `(← readReg _)` inside a Bool guard costs a hypothesis even if the
  value is irrelevant (e.g. Ext_Zca reads misa despite pc[1]=0).
- `Int.tmod` bridge from `pc.toNat % 4 = 0`: `(Int.ofNat_tmod _ _).symm`
  with `show ((4:Nat):Int) = Int.ofNat 4` — the `↑4` form must match
  exactly. Sub-lemma widths can surface as `Int.toNat 4`, not `4` —
  restate via `have h' : … (Int.toNat 4) … := h` so `rw` matches.
- Width-generic clones of `split_misaligned`-style lemmas must return
  the split width as an **Int literal** (`(1, (8:Int))`), not the
  Nat-coerced `(1, ↑8)` a generic `(w:Int)` specializes to — the
  loop-unfold template inherited from Fetch matches on the literal.
  Bridge with `rw [show ((8:Nat):Int) = (8:Int) from rfl]` on the
  composed hypothesis. `norm_num` is not in these files' import set —
  use `rfl`/`decide`/explicit `show` for cast collapses. (MemLoad.lean)

## Store execute-level lemmas (MemStore/ExecuteStore.lean)

- `data.isLt` normalization drifted: for `data : BitVec (8*4)` the old
  `have hlt : data.toNat < 2^64 := by … simpa using data.isLt` no longer
  reaches `2^64` (isLt now gives `< 2^(8*4)` which simp reduces to
  `2^32`). The `hwval` extract-collapse proofs in `vmem_write_addr_{4,2}`
  broke on a fresh toolchain. Fix: state the bound at the *true* width
  (`< 2^32` / `2^16` / `2^8`) and close the residual `mod` goal with
  `omega` instead of the two-step `rw/exact Nat.mod_eq_of_lt`. The
  `data.toNat % 2^(w-1+1) % 2^(8w)` shape is `omega`-solvable once the
  correct `<`-bound is in context.
- **Genericity WON for `vmem_write_addr`.** One `vmem_write_addr_w` over
  `(w : Nat)` takes the whole lower chain as ABSTRACT hyps: `htr`
  (translateAddr, use `translateAddr_machine_store` directly — it already
  concludes `Physaddr (zero_extend a)`), `hea`/`hmwv` stated on **plain**
  `Physaddr a` (NOT `zero_extend a`), and `hwval`. The `zero_extend a` in
  the goal's paddr is folded to `a` by putting `BitVec.setWidth_eq a` in
  the `simp only` set, so `hea`/`hmwv` must be on plain `a` to `rw`. The
  per-width `show ((w:Nat):Int).toNat = w` collapses become the single
  `Int.toNat_natCast`. `vmem_write_addr_1` is a 6-line instantiation.
- Store side needs its OWN generic split lemma: `split_on_page_boundary`
  is width-generic but ExecuteLoad's `split_on_page_boundary_data_w`
  (and `and_page_mask_toNat`) live DOWNSTREAM of MemStore in the import
  graph — cannot import. Cloned as `split_on_page_boundary_store_w` /
  `and_page_mask_toNat_store` in MemStore, built on the local
  `and_page_mask_shift`. Both return `((w : Int), 0)`.
- The width-1 lower-chain lemmas (`mem_write_ea_1`, `mem_write_value_1`)
  take NO `halign` argument (width 1 is trivially aligned) — passing
  `halign` makes `apply`/`have :=` over-apply and yields the cryptic
  "Function expected at … but this term has type … = …".
- ExecuteLoad.lean / MemStore.lean / ExecuteStore.lean are **standalone**
  files — NOT in `Vsa.lean`'s import graph. They are verified only via
  `lake env lean Vsa/Sim/X.lean`. To import one from another (e.g.
  ExecuteStore imports MemStore), you must `lake build Vsa.Sim.MemStore`
  first to produce the `.olean`, else `lake env lean` errors "object file
  … does not exist".
- `execute_STORE`'s `assert (width ≤b xlen_bytes)`: `≤b` is
  `decide (· ≤ ·)` and `xlen_bytes = if xlen=32 then 4 else 8 : Int`, so
  the comparison coerces `width : Nat` to `Int`. Discharge with
  `simp only [Functions.xlen_bytes, decide_eq_true_eq]; omega` (needs
  `hwle : width ≤ 8`).
- The `data` slice in `execute_STORE` (`extractLsb rs2 (width*8-1) 0`)
  elaborates to `BitVec.setWidth (8*width) (Sail.BitVec.extractLsb …)` —
  Lean auto-inserts the `setWidth` coercion to hit `BitVec (8*width)`.
  State the abstract `hwrite` with `Sail.BitVec.extractLsb vdata
  ((width *i 8) -i 1) 0`; the `setWidth` wrapper is added automatically
  and unifies.
- `vmem_write` (and `execute_STORE`) close with an outer
  `SailME.run`/`ExceptT` result-match; after `rw`-ing the inner
  `.run … = .ok (.Ok true) m'` fact, a trailing `simp only [EStateM.pure]`
  reduces the residual `match … | Ok x => pure RETIRE_SUCCESS` /
  `| Except.ok e => …` matcher.

## Load execute-level lemmas (ExecuteLoad.lean)

- The `≤b` assert discriminant does not rewrite by a Bool hypothesis under
  a monadic bind: `x ≤b y` is `decide (x ≤ y)` notation, and
  `execute_LOAD`'s `assert (width ≤b xlen_bytes)` renders as an `ite`
  buried in a bind — `simp only [h]`, `rw [if_pos h]`, `split` all fail.
  Recipe: `rw [show execute (instruction.LOAD …) = execute_LOAD … from
  rfl]` (outer 32-way match is `rfl` on a concrete ctor), `unfold
  execute_LOAD`, then ONE `simp only [LeanRV64DExecutable.assert,
  PreSail.assert, hwidth, if_true, …]` — post-`unfold` the discriminant is
  at the head and the hypothesis fires.
- `vmem_read_addr`'s `access_width` feeds `translate_and_read_value` as
  `(↑w).toNat`, not `w` (`split_on_page_boundary` returns `Int`). A leaf
  lemma stated at width `w` will NOT `rw` until `simp only
  [Int.toNat_natCast]` runs first — it is `rfl` and `@[simp]` but blocked
  from fixpoint firing by the surrounding term.
- `rw` cannot rewrite `updateSubrange`/`zeros` results whose width index
  is `(8 * ↑w).toNat` (dependent type index ⇒ motive errors). Escapes:
  (a) `apply BitVec.eq_of_toNat_eq` FIRST — on the Nat goal the widths are
  defeq-plain; (b) at use sites replace `rw [lemma]` with
  `exact congrArg (fun x => EStateM.Result.ok (Result.Ok x) σ) lemma` —
  congrArg+exact go through defeq, sidestepping the motive.
- Available in this import set: `Nat.two_pow_pos`, `Nat.mod_mod`
  (`(a%n)%n = a%n`), `Nat.and_zero` (`x &&& 0 = 0` — NOT `Nat.zero_and`;
  `x &&& 0` parses with the subtraction on its left as operand),
  `Nat.mod_eq_of_lt`, `omega`. NOT available: `norm_num`, `push_cast`,
  `ring`, `dvd_refl`, `Int.toNat_ofNat`, `Nat.cast_ofNat`, `set` tactic.

## Record-update `let` bombs (Frame.lean)

- `{compound with field := …}` where the base is a non-atomic term
  elaborates to `let __src := compound; …` — the written field keeps
  the original `compound` form while copied fields use `__src`. This
  defeats `apply` of record-eta lemmas like
  `{σ with regs := σ.regs.insert r v}` (first-order unification can't
  build a constructor for the `let`-bound base). `unfold`/`simp only`
  on the abbrev only over-flatten to one `{σ with regs := <chain>}`,
  equally unusable for single-insert chaining. Escape: build the proof
  term by explicit iterated application and close with `exact` (full
  defeq zeta-reduces the `let`), pinning binders via `(σ := …)` named
  args. This is why `noncomputable abbrev sigmaTick` won't peel with
  `goodstate_frame` while plain `abbrev sigmaPost` does.
- Tactic macros that `apply Foo (hr := by decide)` with metavariable
  args: elaborate `by decide` only AFTER `apply` unifies the
  conclusion (use `apply Foo (hr := by decide)` in `repeat' first`
  form post-unification, never `(r := _) (v := _)` placeholders — they
  elaborate the `by` block against unassigned metas and fail).

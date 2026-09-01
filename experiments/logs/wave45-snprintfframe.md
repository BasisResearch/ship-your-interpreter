# Wave 45 — snprintfframe lane

HEAD 80aab36 (wave 44). Lane: factor `SnprintfFrameContract` + discharge/reduce
`SnprintfContract` (JmpSpec.lean:1450) = runtime_error 0x80002da8 → jal longjmp
0x8000703c, through the two snprintf calls (frame/footprint only).

## Findings (probe confirmed)

- The landed `snprintf_lld_spec` (SnprintfSpec42) IS byte-exact `%lld`
  (x12 pinned = 0x800192c0). Its POST already carries the format-generic
  pointwise frame (lines 190-192): `∀ a, ¬(vsp−88 ≤ a < vsp+864) →
  ¬(d ≤ a < d+len+1) → mem'[a]? = mem[a]?` — i.e. writes ⊆ stack ∪ [d,d+len+1).
  That IS the footprint fact. BUT the two runtime_error calls are:
  - call #1 @0x80002dc8: caller-inherited fmt (a2 forwarded, arbitrary) — into `body` on sp.
  - call #2 @0x80002de4: fixed fmt 0x80019318 = "runtime error [line %d]: %s"
    (%d + %s conversions, unverified formatter paths) — into err_msg at s0+224.
  NEITHER is %lld. So `snprintf_lld_spec` cannot be instantiated for either.
  ⇒ format-generic frame contract is a genuine NAMED premise (Law 2). Confirmed.

- STRUCTURAL OBSERVATION on `SnprintfContract` itself: its POST asserts the 15
  jmp_buf read64 slots (inp+16+8k = setjmp values sv), but its PRE only has
  `mem = m0` + WinRAM — it does NOT carry those read64 facts. So the segment
  CANNOT prove them from the pre alone. The setjmp values live in m0 but the
  pre never says so. ⇒ the discharge needs the entry read64 slots as NAMED
  premises (a `JmpBufAt m0 inp …` residual). Then they survive both snprintf
  writes (disjoint: body on sp, err_msg at s0+224, jmp_buf at inp+16) and the
  three decode segs (disjoint stack) by `read64_agreeP`.

## Plan
1. `Vsa/Sim/rows/SnprintfFrame.lean`: `SnprintfFrameContract` named-field
   structure — Triple from snprintf ABI entry (a0=dst,a1=n,ra=link) to return
   (PC=link,sp restored), post = named-field `SnprintfFrameOut` (frame AgreeP on
   the complement of [dst,dst+n), output-neutral, ABI, GoodState/tick/minstret).
2. `Vsa/Sim/rows/ErrSegSnprintf.lean`: 3 `#derive_case` segs
   (prologue/between/epilogue) + jal-longjmp seam; `snprintfContract_of`
   composes prologue ≫ FC#1 ≫ between ≫ FC#2 ≫ epilogue ≫ jal into
   `SnprintfContract.segment`, threading jmp_buf preservation. Land maximal
   green prefix + named residuals.

## Progress
(appended per landing)

## §LANDED (coordinator, end of wave 45)

`rows/SnprintfFrame.lean` (SnprintfFrameContract + read64_pres) is GREEN,
wired into Vsa.lean + check_all (875/875).  The §plan item 2 (rows/ErrSegSnprintf
3 segs + composition) stalled with 11 elaboration errors mid-flight; the file
is quarantined verbatim at `experiments/wip/ErrSegSnprintf.lean.w45` — resume
from the two findings above (format-generic premise named; jmp_buf read64
entry slots as named `JmpBufAt` residual).

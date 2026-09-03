(assert (= (ld4 (mm s0) #x0000000080019f58) #x00000000fffe94b0))
(assert (= (ld4 (mm s0) #x0000000080019f5c) #x00000000fffe94bc))
(assert (= (ld4 (mm s0) #x0000000080019f60) #x00000000fffe94c8))
(assert (= (ld4 (mm s0) #x0000000080019f64) #x00000000fffe94d4))
(assert (= (ld4 (mm s0) #x0000000080019f68) #x00000000fffe94dc))
(assert (= (ld4 (mm s0) #x0000000080019f6c) #x00000000fffe9524))
(assert (= (ld4 (mm s0) #x0000000080019f70) #x00000000fffe9590))
(assert (= (ld4 (mm s0) #x0000000080019f74) #x00000000fffe9604))
(assert (= (ld4 (mm s0) #x0000000080019f78) #x00000000fffe9688))
(assert (= (ld4 (mm s0) #x0000000080019f7c) #x00000000fffe9258))
(assert (= (ld4 (mm s0) #x0000000080019f84) #x00000000fffe9904))
(assert (= (ld4 (mm s0) #x0000000080019f88) #x00000000fffe995c))
(assert (= (ld4 (mm s0) #x0000000080019f8c) #x00000000fffe98b0))
(assert (= (ld4 (mm s0) #x0000000080019f90) #x00000000fffe9858))
(assert (= (ld4 (mm s0) #x0000000080019f94) #x00000000fffe9800))
(assert (= (ld4 (mm s0) #x0000000080019f98) #x00000000fffe99a4))
(assert (= (ld4 (mm s0) #x0000000080019f9c) #x00000000fffe97b0))
(assert (= (ld4 (mm s0) #x0000000080019fa0) #x00000000fffe99a4))
(assert (= (ld4 (mm s0) #x0000000080019fa4) #x00000000fffe9760))
(assert (= (ld4 (mm s0) #x0000000080019fa8) #x00000000fffe96a4))
(assert (= (ld4 (mm s0) #x0000000080019fac) #x00000000fffe96a4))
(assert (= (ld4 (mm s0) #x0000000080019fb0) #x00000000fffe96a4))
(assert (= (ld4 (mm s0) #x0000000080019fb4) #x00000000fffe96a4))
(assert (= (ld4 (mm s0) #x0000000080019fb8) #x00000000fffea1b8))
(assert (= (ld4 (mm s0) #x0000000080019fbc) #x00000000fffea120))
(assert (= (ld4 (mm s0) #x0000000080019fc0) #x00000000fffea1d4))
(assert (= (ld4 (mm s0) #x0000000080019fc4) #x00000000fffea230))
(assert (= (ld4 (mm s0) #x0000000080019fc8) #x00000000fffea084))
(assert (= (ld4 (mm s0) #x0000000080019fcc) #x00000000fffea27c))
(assert (= (ld4 (mm s0) #x0000000080019fd0) #x00000000fffea168))
(assert (= (ld4 (mm s0) #x0000000080019fd4) #x00000000fffea0e0))
(assert (= (ld4 (mm s0) #x0000000080019fd8) #x00000000fffea100))
; EvalEntry.stackBudget / stackOK: sp sits inside the stack with headroom
(assert (bvule (bvadd SL_lo #x0000000000001100) (select (rr s0) #x0000000000000002)))
(assert (bvule (select (rr s0) #x0000000000000002) SL_hi))
; the arm's own frame lies ABOVE sp and inside the stack too: the span starts
; after the prologue has lowered sp, so its spills are at sp+k for k < frame,
; and those belong to the frame the caller's own `StackOK` already placed
(assert (bvule (bvadd (select (rr s0) #x0000000000000002) #x0000000000001100) SL_hi))
(assert (bvult SL_lo SL_hi))
; the heap arena is disjoint from the stack window
(assert (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)))
(assert (bvult A_lo A_hi))
; `InterpCodeLoaded`: the code image is disjoint from BOTH — without this the
; code-preservation post cannot even be stated (an address in the code region
; would be allowed to sit inside the stack)
(assert (or (bvult SL_hi #x0000000080000000) (bvuge SL_lo #x0000000080018be0)))
(assert (or (bvult A_hi #x0000000080000000) (bvuge A_lo #x0000000080018be0)))
; the stack sits above the first megabyte, so `sp - frame` cannot underflow,
; and both regions are inside the 4 GB the HTIF image addresses, so `sp + frame`
; cannot wrap either (without this the solver puts the stack at the top of the
; address space and wraps a spill into the code image)
(assert (bvule #x0000000000100000 SL_lo))
(assert (bvult SL_hi #x0000000100000000))
(assert (bvult A_hi #x0000000100000000))
; and the layout invariant itself.  A query needs it for the same reason a
; summary obligation does: without it the solver picks a seventeen-byte arena,
; `A_hi - 32` underflows, and every `Arena.contains` hypothesis goes vacuous —
; which is exactly what produced fifteen spurious refutations.
(assert (INV s0))
; `EvalEntry.sret_ram` / `sret_align` / `sret_stack_disjoint`: the caller's
; 24-byte return buffer, passed in a0, is a real RAM address, 8-aligned, and
; either below the stack window or above `sp`.  The arm STORES the boxed
; result through it, so without this the store address is unconstrained and
; the model puts it in the code image.
(assert (bvule #x0000000080000000 (select (rr s0) #x000000000000000a)))
(assert (bvule (bvadd (select (rr s0) #x000000000000000a) #x0000000000000018) #x0000000100000000))
(assert (= (bvand (select (rr s0) #x000000000000000a) #x0000000000000007) #x0000000000000000))
(assert (or (bvule (bvadd (select (rr s0) #x000000000000000a) #x0000000000000018) SL_lo) (bvule (select (rr s0) #x0000000000000002) (select (rr s0) #x000000000000000a))))
; and the buffer is disjoint from the code image (`sret_vicode_disjoint`,
; widened to the whole loaded text)
(assert (or (bvule (bvadd (select (rr s0) #x000000000000000a) #x0000000000000018) #x0000000080000000) (bvule #x0000000080018be0 (select (rr s0) #x000000000000000a))))

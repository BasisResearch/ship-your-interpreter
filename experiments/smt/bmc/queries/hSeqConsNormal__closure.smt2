(set-logic ALL)
; ---------------------------------------------------------------------------
; Machine state, PURELY in the bitvector theory.  Registers and addresses are
; 64-bit two's complement (so arithmetic WRAPS, as RV64 does) and memory is a
; byte array indexed by a 64-bit address.  There is no `Int` anywhere: the
; earlier encoding modelled registers as mathematical integers and bridged to
; bitvectors with `int2bv`/`bv2int` at every load, store, shift and bitwise op,
; which (a) silently dropped 64-bit wraparound and (b) coupled the arithmetic
; solver to the bit-blaster — 19350 `bv-bit2core` axioms on a 34 KB obligation.
; Every span reflects to a FINITE term, so in pure QF_ABV the whole thing is
; bit-blastable.
; ---------------------------------------------------------------------------
(declare-datatypes () ((MState (mst (mm (Array (_ BitVec 64) (_ BitVec 8))) (rr (Array (_ BitVec 64) (_ BitVec 64)))))))
; A word outside `decodeM`'s coverage that `rawRegVal` also does not give exact
; semantics for.  Uninterpreted, so it OVER-approximates: a post proved through
; it holds whatever the instruction does.  The alternative -- `mkLine`'s
; `addi x0, x0, 0` fallback -- is a silent lie.
(declare-fun unmodelled_step (MState) MState)
(define-fun ld1 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ zero_extend 56) (select m a)))
(define-fun ld2 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ zero_extend 48) (concat (select m (bvadd a #x0000000000000001)) (select m a))))
(define-fun ld4 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ zero_extend 32) (concat (select m (bvadd a #x0000000000000003)) (select m (bvadd a #x0000000000000002)) (select m (bvadd a #x0000000000000001)) (select m a))))
(define-fun ld8 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) (concat (select m (bvadd a #x0000000000000007)) (select m (bvadd a #x0000000000000006)) (select m (bvadd a #x0000000000000005)) (select m (bvadd a #x0000000000000004)) (select m (bvadd a #x0000000000000003)) (select m (bvadd a #x0000000000000002)) (select m (bvadd a #x0000000000000001)) (select m a)))
(define-fun ld1s ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 56) (select m a)))
(define-fun ld2s ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 48) (concat (select m (bvadd a #x0000000000000001)) (select m a))))
(define-fun ld4s ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 32) (concat (select m (bvadd a #x0000000000000003)) (select m (bvadd a #x0000000000000002)) (select m (bvadd a #x0000000000000001)) (select m a))))
(define-fun w32 ((v (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 32) ((_ extract 31 0) v)))
(declare-fun callee_2147500000 (MState) MState)
(define-fun G_lo () (_ BitVec 64) #x000000008001ad00)
(define-fun G_hi () (_ BitVec 64) #x000000008001c168)
(declare-const SL_lo (_ BitVec 64))
(declare-const SL_hi (_ BitVec 64))
(declare-const A_lo (_ BitVec 64))
(declare-const A_hi (_ BitVec 64))
(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))
(declare-const s0 MState)
(declare-const g0 Bool)
(assert (= g0 true))
(declare-const m0 MState)
(assert (= m0 s0))
(declare-const i1 MState)
(assert (= i1 (mst (mm m0) (store (rr m0) #x000000000000000f (ld8 (mm m0) (bvadd (select (rr m0) #x0000000000000010) #x0000000000000008))))))
(declare-const i2 MState)
(assert (= i2 (mst (mm i1) (store (rr i1) #x000000000000000e (bvshl (select (rr i1) #x0000000000000008) #x0000000000000003)))))
(declare-const i3 MState)
(assert (= i3 (mst (mm i2) (store (rr i2) #x000000000000000d (bvadd (select (rr i2) #x0000000000000002) #x0000000000000090)))))
(declare-const i4 MState)
(assert (= i4 (mst (mm i3) (store (rr i3) #x000000000000000f (bvadd (select (rr i3) #x000000000000000f) (select (rr i3) #x000000000000000e))))))
(declare-const i5 MState)
(assert (= i5 (mst (mm i4) (store (rr i4) #x000000000000000b (ld8 (mm i4) (bvadd (select (rr i4) #x000000000000000f) #x0000000000000000))))))
(declare-const i6 MState)
(assert (= i6 (mst (mm i5) (store (rr i5) #x000000000000000c (bvadd (select (rr i5) #x0000000000000013) #x0000000000000000)))))
(declare-const i7 MState)
(assert (= i7 (mst (mm i6) (store (rr i6) #x000000000000000a (bvadd (select (rr i6) #x0000000000000012) #x0000000000000000)))))
(declare-const i8 MState)
(assert (= i8 (mst (store (store (store (store (store (store (store (store (mm i7) (bvadd (bvadd (select (rr i7) #x0000000000000002) #x0000000000000000) #x0000000000000000) ((_ extract 7 0) (select (rr i7) #x0000000000000010))) (bvadd (bvadd (select (rr i7) #x0000000000000002) #x0000000000000000) #x0000000000000001) ((_ extract 15 8) (select (rr i7) #x0000000000000010))) (bvadd (bvadd (select (rr i7) #x0000000000000002) #x0000000000000000) #x0000000000000002) ((_ extract 23 16) (select (rr i7) #x0000000000000010))) (bvadd (bvadd (select (rr i7) #x0000000000000002) #x0000000000000000) #x0000000000000003) ((_ extract 31 24) (select (rr i7) #x0000000000000010))) (bvadd (bvadd (select (rr i7) #x0000000000000002) #x0000000000000000) #x0000000000000004) ((_ extract 39 32) (select (rr i7) #x0000000000000010))) (bvadd (bvadd (select (rr i7) #x0000000000000002) #x0000000000000000) #x0000000000000005) ((_ extract 47 40) (select (rr i7) #x0000000000000010))) (bvadd (bvadd (select (rr i7) #x0000000000000002) #x0000000000000000) #x0000000000000006) ((_ extract 55 48) (select (rr i7) #x0000000000000010))) (bvadd (bvadd (select (rr i7) #x0000000000000002) #x0000000000000000) #x0000000000000007) ((_ extract 63 56) (select (rr i7) #x0000000000000010))) (rr i7))))
(declare-const ra9 MState)
(assert (= ra9 (mst (mm i8) (store (rr i8) #x0000000000000001 #x0000000080003378))))
(declare-const b0 MState)
(assert (= b0 (callee_2147500000 ra9)))
(declare-const g10x Bool)
(assert (= g10x g0))
; residual-specific premises from the Lean constructor
; only inputs that REACH the exit PC: without this the `ite` merge
; falls through to the last arrival for an input no guard covers, and the
; resulting state is one the machine is never in -- spurious REFUTED.
(assert g10x)
; mined clause set for every summary
; @@ASSUME@@
(define-fun state_exit () MState b0)
(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) (mm state_exit))
; @@POST@@

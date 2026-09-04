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
(declare-fun loop_2147496412 (MState) MState)
(declare-fun loopcond_2147496412 (MState) Bool)
(declare-fun loopexit_2147496412 (MState) (_ BitVec 64))
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
(declare-const b0 MState)
(assert (= b0 m0))
(declare-const g1q Bool)
(assert (= g1q (and g0 (not (bvsge #x0000000000000000 (select (rr b0) #x000000000000000f))))))
(declare-const g2x Bool)
(assert (= g2x (and g0 (bvsge #x0000000000000000 (select (rr b0) #x000000000000000f)))))
(declare-const g3 Bool)
(assert (= g3 g1q))
(declare-const m3 MState)
(assert (= m3 b0))
(declare-const m4 MState)
(assert (= m4 (loop_2147496412 m3)))
(declare-const g5x Bool)
(assert (= g5x (and g3 (= (loopexit_2147496412 m3) #x0000000080003254))))
; residual-specific premises from the Lean constructor
(assert (= (select (rr s0) #x000000000000000f) #x0000000000000000))
; only inputs that REACH the exit PC: without this the `ite` merge
; falls through to the last arrival for an input no guard covers, and the
; resulting state is one the machine is never in -- spurious REFUTED.
(assert (or g2x g5x))
; mined clause set for every summary
; @@ASSUME@@
(define-fun state_exit () MState (ite g2x b0 m4))
(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) (mm state_exit))
; @@POST@@

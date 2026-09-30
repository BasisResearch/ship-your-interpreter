import Vsa.Sim.MemcpySites2
import Vsa.Sim.MemcpySpec
import Vsa.Triple
import Vsa.Sim.ObsAvoid

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem extractLsb'_ldData8 (c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8) (k : Nat) (hk : k < 8)
    (ck : BitVec 8)
    (hck : [c0, c1, c2, c3, c4, c5, c6, c7][k]? = some ck) :
    (ldData8 c0 c1 c2 c3 c4 c5 c6 c7).extractLsb' (8 * k) 8 = ck := by
  show ((((((((c7 +++ c6) +++ c5) +++ c4) +++ c3) +++ c2) +++ c1) +++ c0).extractLsb' (8 * k) 8) = ck
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  match k, hk, hck with
  | 0, _, hck | 1, _, hck | 2, _, hck | 3, _, hck
  | 4, _, hck | 5, _, hck | 6, _, hck | 7, _, hck =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hck
    subst hck
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.reduceMul]
    rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
    repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
    congr 1 <;> omega

end Vsa.Sim

import Vsa.Sim.UntilSequence
import Vsa.Sim.RamReadData
import Vsa.Sim.RamReadSplit

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

abbrev SplitReadResult (w : Nat) :=
  Result ((BitVec (8 * w)) × Unit) (physaddr × ExceptionType)

abbrev SplitReadState (n d : Nat) := BitVec (8 * (n : Int) * (d : Int)).toNat × Bool × Nat

/-- Address calculation used by the actual split-read loop. -/
def ramChunkAddress (a : BitVec 64) (d i : Nat) : physaddr :=
  physaddr.Physaddr (BitVec.addInt a ((i : Int) * (d : Int)))

/-- The actual loop's little-endian insertion operation. -/
def splitReadInsert (n d i : Nat) (data : BitVec (8 * (n : Int) * (d : Int)).toNat) (v : BitVec (8 * d)) :
    BitVec (8 * (n : Int) * (d : Int)).toNat :=
  let updated : BitVec (8 * n * d) :=
    Sail.BitVec.updateSubrange (data.setWidth (8 * n * d))
      ((8 * ((i : Int) + 1) * (d : Int) - 1).toNat)
      ((8 * (i : Int) * (d : Int)).toNat) v
  updated.setWidth (8 * (n : Int) * (d : Int)).toNat


/-- Assembly after the first i chunks, using the same insertion as Sail. -/
def splitReadAccum (n d : Nat) (values : Nat → BitVec (8 * d)) : Nat → BitVec (8 * (n : Int) * (d : Int)).toNat
  | 0 => 0
  | i + 1 => splitReadInsert n d i (splitReadAccum n d values i) (values i)

/-- Exact loop state after i chunks. The final iteration retains its index. -/
def splitReadTrace (n d : Nat) (values : Nat → BitVec (8 * d)) (i : Nat) : SplitReadState n d :=
  (splitReadAccum n d values i, decide (n ≤ i), min i (n - 1))

/-- One body of the executable scalar split-read loop. -/
def splitReadBody (a : BitVec 64) (w n d : Nat) :
    SplitReadState n d → SailME (SplitReadResult w) (SplitReadState n d) :=
  let N : Int := n
  let split_width : Int := d
  let paddr_bits := a
  let last : Int := N - 1
  let step : Int := 1
  let access := MemoryAccessType.Load mem_payload.Data
  let priv := Privilege.Machine
  let rk := read_kind.Read_plain
  let meta' := false
  fun (data, finished, i) => do
        LeanRV64DExecutable.assert true "loop dummy assert"
        let offset := i
        let paddr := (physaddr.Physaddr (BitVec.addInt paddr_bits (offset *i split_width)))
        match (← (pmpCheck paddr split_width access priv)) with
        | .some e =>
          SailME.throw ((Err (paddr, e)) : (Result ((BitVec (8 * w)) × Unit) (physaddr × ExceptionType)))
        | none => (pure ())
        let split_data ← do
          if ((← (within_mmio_readable paddr split_width)) : Bool)
          then
            (do
              match (← (mmio_read access paddr split_width)) with
              | .Err e =>
                SailME.throw ((Err e) : (Result ((BitVec (8 * w)) × Unit) (physaddr × ExceptionType)))
              | .Ok mmio_data => (pure mmio_data))
          else
            (do
              let (ram_data, _meta) ← do (read_ram rk paddr split_width meta')
              (pure ram_data))
        let data : (BitVec (8 * N * split_width)) :=
          (Sail.BitVec.updateSubrange (data.setWidth (8 * n * d)) (((8 *i (offset +i 1)) *i split_width) -i 1)
            ((8 *i offset) *i split_width) split_data)
        let data := data.setWidth (8 * (n : Int) * (d : Int)).toNat
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (data, finished, i))

/-- Read checks and the actual RAM value at one selected chunk. -/
structure SplitReadChunk (σ : Vsa.Machine.MState) (a : BitVec 64)
    (d i : Nat) (v : BitVec (8 * d)) : Prop where
  pmp : (pmpCheck (ramChunkAddress a d i) d
    (MemoryAccessType.Load mem_payload.Data) Privilege.Machine).run σ = .ok none σ
  mmio : (within_mmio_readable (ramChunkAddress a d i) d).run σ = .ok false σ
  ram : (Functions.read_ram read_kind.Read_plain (ramChunkAddress a d i)
    d false).run σ = .ok (v, ()) σ

/-- A checked chunk advances the concrete loop trace once. -/
theorem splitReadBody_trace (σ : Vsa.Machine.MState) (a : BitVec 64) (w n d i : Nat)
    (values : Nat → BitVec (8 * d)) (hi : i < n)
    (hc : SplitReadChunk σ a d i (values i)) :
    ExceptT.run (splitReadBody a w n d (splitReadTrace n d values i)) σ =
      .ok (.ok (splitReadTrace n d values (i + 1))) σ := by
  have hpmp := hc.pmp
  have hmmio := hc.mmio
  have hram := hc.ram
  have hindex : min i (n - 1) = i := Nat.min_eq_left (by omega)
  simp only [EStateM.run, ramChunkAddress] at hpmp hmmio hram
  simp only [splitReadBody, splitReadTrace, hindex, ExceptT.run,
    LeanRV64DExecutable.assert, PreSail.assert,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.pure,
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
    Functor.map, EStateM.map, EStateM.bind, pure, EStateM.pure,
    if_true, Int.toNat_natCast]
  rw [hpmp]
  simp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  rw [hmmio]
  simp only [EStateM.bind, EStateM.map, ExceptT.bindCont, Bool.false_eq_true, if_false]
  rw [hram]
  simp only [EStateM.pure]
  change EStateM.Result.ok (Except.ok
    (splitReadInsert n d i (splitReadAccum n d values i) (values i),
      (if i == ((n : Int) - 1).toNat then (true, i) else (decide (n ≤ i), ((i : Int) + 1).toNat)).1,
      (if i == ((n : Int) - 1).toNat then (true, i) else (decide (n ≤ i), ((i : Int) + 1).toNat)).2)) σ = _
  have hnat : ((n : Int) - 1).toNat = n - 1 := by omega
  have hinc : ((i : Int) + 1).toNat = i + 1 := by omega
  have hbefore : ¬ n ≤ i := by omega
  by_cases hlast : i + 1 = n
  · have he : i = n - 1 := by omega
    simp [hnat, he, splitReadAccum]
    omega
  · have he : i ≠ n - 1 := by omega
    have hn : ¬ n ≤ i + 1 := by omega
    have hm : min (i + 1) (n - 1) = i + 1 := Nat.min_eq_left (by omega)
    simp [hnat, hinc, hbefore, he, hn, hm, splitReadAccum]

/-- Every chunk supplied by the trace is read once, with exact accumulated bytes. -/
theorem splitReadLoop_trace (σ : Vsa.Machine.MState) (a : BitVec 64) (w n d : Nat)
    (values : Nat → BitVec (8 * d))
    (hc : ∀ i, i < n → SplitReadChunk σ a d i (values i)) :
    ExceptT.run (untilFuelM n (fun x : SplitReadState n d => pure x.2.1)
      (splitReadTrace n d values 0) (splitReadBody a w n d)) σ =
      .ok (.ok (splitReadTrace n d values n)) σ := by
  apply untilFuelM_sequence σ n (splitReadTrace n d values) (splitReadBody a w n d)
  · intro i hi
    exact splitReadBody_trace σ a w n d i values hi (hc i hi)
  · intro i _ hi
    have he : (n ≤ i) ↔ (i = n) := by omega
    by_cases heq : i = n <;>
      simp [splitReadTrace, he, heq, ExceptT.run, pure, ExceptT.pure, ExceptT.mk, EStateM.pure]

#print axioms splitReadLoop_trace

#print axioms splitReadBody_trace
end Vsa.Sim

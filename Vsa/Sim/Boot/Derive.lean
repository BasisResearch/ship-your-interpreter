import Vsa.Sim.Boot.Witness
import Std.Data.HashMap

/-!
# Deriving boot-witness data from a trace

Executable generator code: from a boot trace (`script`, packed write log, registers) and the
program, compute the data a `Witness` carries besides the trace. Nothing here is trusted; the
kernel checks every derived value through `Witness.Ok`.

- `runs`: the last writer and value of every written byte, grouped into runs of at most 64
  contiguous bytes, in a balanced search tree.
- heap: `top` and the break from the allocator state, the chunk walk from the heap start,
  the free-bin chains.
- `own`: the global frame, its arrays and keys read from memory; the AST extents are the heap
  chunks the represented program reaches.
-/

namespace Vsa.Sim.Boot.Derive

open Vsa.While Vsa.Sim.DlHeap Vsa.Sim.LayoutInstance

instance : Inhabited Run := ⟨⟨0, 0, 0⟩⟩

/-- Last writer index and byte value of every written byte. -/
def lastWriters (L : PackedLog) : Std.HashMap Nat (Nat × Nat) :=
  (List.range L.len).foldl (fun m i =>
    let r := L.raw i
    let a := r % 2 ^ 32
    let w := (r >>> 32) % 16
    (List.range w).foldl (fun m j =>
      match writeEntryByte (L.entry i) (a + j) with
      | some b => m.insert (a + j) (i, b.toNat)
      | none => m) m) ∅

/-- Split sorted addresses into maximal contiguous segments of at most `max` bytes. -/
def segments (max : Nat) (xs : List Nat) : List (Nat × Nat) :=
  (xs.foldl (fun (acc : List (Nat × Nat)) x =>
    match acc with
    | (b, n) :: rest => if b + n == x && n < max then (b, n + 1) :: rest else (x, 1) :: acc
    | [] => [(x, 1)]) []).reverse

def mkRun (m : Std.HashMap Nat (Nat × Nat)) (seg : Nat × Nat) : Run :=
  ⟨seg.1, seg.2, (List.range seg.2).foldl (fun acc j =>
    let (k, b) := m.getD (seg.1 + j) (0, 0)
    acc ||| ((k + b * 2 ^ 24) <<< (32 * j))) 0⟩

def buildTree (leaves : Array Run) (lo : Nat) : Nat → RunTree
  | 0 => .leaf leaves[lo]!
  | 1 => .leaf leaves[lo]!
  | n + 2 =>
    let k := (n + 2) / 2
    .node leaves[lo + k]!.base (buildTree leaves lo k) (buildTree leaves (lo + k) (n + 2 - k))
termination_by n => n
decreasing_by all_goals omega

def runs (L : PackedLog) : RunTree :=
  let m := lastWriters L
  let keys := (m.toList.map (·.1)).toArray.qsort (· < ·)
  let leaves := (segments 64 keys.toList).toArray.map (mkRun m)
  buildTree leaves 0 leaves.size

def r64 (v : Nat → Option (BitVec 8)) (a : Nat) : Nat := (readLEv v a 8).getD 0

/-- The dlmalloc chunk walk from `p` to `top`. -/
def walk (v : Nat → Option (BitVec 8)) (top : Nat) : Nat → Nat → List Chunk
  | 0, _ => []
  | fuel + 1, p =>
    if top ≤ p then []
    else
      let sz := chunkSize (r64 v (p + 8))
      if sz = 0 then []
      else ⟨p, sz, prevInuse (r64 v (p + sz + 8))⟩ :: walk v top fuel (p + sz)

/-- The chain of free chunks in bin `i`. -/
def binChain (v : Nat → Option (BitVec 8)) (i : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, q => if q == binAt i then [] else q :: binChain v i fuel (r64 v (q + 16))

def bins (v : Nat → Option (BitVec 8)) : List (List Nat) :=
  let L := (List.range numBins).map fun i =>
    if i = 0 then [] else binChain v i 100000 (r64 v (binAt i + 16))
  if L.all List.isEmpty then [] else L

/-! ### Addresses the represented program reaches -/

mutual

partial def expr (v : Nat → Option (BitVec 8)) (a : Nat) (acc : Array Nat) : Array Nat :=
  let acc := acc.push a
  let tag := (readLEv v a 4).getD 99
  let p8 := r64 v (a + 8)
  let p16 := r64 v (a + 16)
  let p24 := r64 v (a + 24)
  match tag with
  | 1 | 4 => acc.push p8
  | 5 => expr v p16 (acc.push p8)
  | 6 | 7 => expr v p24 (expr v p16 acc)
  | 8 => expr v p16 acc
  | 9 =>
    let n := (readLEv v (a + 24) 4).getD 0
    let acc := if n = 0 then acc else acc.push p16
    (List.range n).foldl (fun acc j => expr v (r64 v (p16 + 8 * j)) acc) (expr v p8 acc)
  | 10 =>
    let acc := if p8 = 0 then acc else acc.push p8
    let n := (readLEv v (a + 24) 4).getD 0
    let acc := if n = 0 then acc else acc.push p16
    let acc := (List.range n).foldl (fun acc j => acc.push (r64 v (p16 + 8 * j))) acc
    stmt v (r64 v (a + 32)) acc
  | _ => acc

partial def stmt (v : Nat → Option (BitVec 8)) (a : Nat) (acc : Array Nat) : Array Nat :=
  let acc := acc.push a
  let tag := (readLEv v a 4).getD 99
  let p8 := r64 v (a + 8)
  let p16 := r64 v (a + 16)
  let p24 := r64 v (a + 24)
  let opt (f : Nat → Array Nat → Array Nat) (p : Nat) (acc : Array Nat) :=
    if p = 0 then acc else f p acc
  match tag with
  | 0 => expr v p8 acc
  | 1 => opt (expr v) p16 (acc.push p8)
  | 2 => stmts v p8 ((readLEv v (a + 16) 4).getD 0) acc
  | 3 => opt (stmt v) p24 (stmt v p16 (expr v p8 acc))
  | 4 => stmt v p16 (expr v p8 acc)
  | 5 => stmt v (r64 v (a + 32)) (opt (expr v) p24 (opt (expr v) p16 (opt (stmt v) p8 acc)))
  | 6 => opt (expr v) p8 acc
  | _ => acc

partial def stmts (v : Nat → Option (BitVec 8)) (a n : Nat) (acc : Array Nat) : Array Nat :=
  let acc := if n = 0 then acc else acc.push a
  (List.range n).foldl (fun acc j => stmt v (r64 v (a + 8 * j)) acc) acc

end

/-- Derived data of a boot witness. -/
structure Data where
  runs : RunTree
  own : BootOwn
  top : Nat
  brkv : Nat
  chunks : List Chunk
  bins : List (List Nat)
  stmts : Nat
  count : Nat

def data (script : Nat) (L : PackedLog) (regs : Nat → BitVec 64) : Data :=
  let t := runs L
  let v := bootView script t
  let top := r64 v topAddr
  let brkv := r64 v brkAddr
  let cs := walk v top 100000 heapStart
  let stmtsA := (regs 11).toNat
  let count := (regs 12).toNat
  let env := r64 v interpObject
  let pn := r64 v (env + 8)
  let pv := r64 v (env + 16)
  let keys := (List.range 3).map fun i => r64 v (pn + 8 * i)
  let names := (List.range 3).map fun i => r64 v (pv + 24 * i + 8)
  let roles := [env, pn, pv] ++ keys
  let reached := stmts v stmtsA count #[]
  let ast := (cs.filter fun c => c.inuse && !roles.contains (c.addr + 16) &&
      reached.any fun a => decide (c.addr + 16 ≤ a ∧ a < c.addr + c.size + 8)).map
    fun c => (c.addr + 16, c.size - 8)
  { runs := t
    own :=
      { env, pn, pv
        cap := (readLEv v (env + 4) 4).getD 0
        key0 := keys[0]!, key1 := keys[1]!, key2 := keys[2]!
        name0 := names[0]!, name1 := names[1]!, name2 := names[2]!
        ast }
    top, brkv
    chunks := cs
    bins := bins v
    stmts := stmtsA
    count }

end Vsa.Sim.Boot.Derive

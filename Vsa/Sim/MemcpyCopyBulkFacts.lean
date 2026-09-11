import Vsa.Sim.MemcpyCopyBulkAccess

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

private def body : List MInstr := (memcpyX6c60FSeg[0]'(by decide)).body

private def block (more : Bool) : BBlock :=
  if more then memcpyX6c60TSeg[0]'(by decide) else memcpyX6c60FSeg[0]'(by decide)

private theorem bodyFacts (dst src r : BitVec 64) (n i : Nat) (m : Mem)
    (loaded : Code.MemcpyLoaded m) (access : BulkAccess dst src i m) :
    ProgFactsM m m (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)) body := by
  chain_facts loaded with "Vsa.Sim.Code.memcpy_at_"
  · exact access.reads 0 (by decide)
  · exact access.reads 1 (by decide)
  · exact access.reads 2 (by decide)
  · exact access.reads 3 (by decide)
  · exact access.reads 4 (by decide)
  · exact access.reads 5 (by decide)
  · exact access.reads 6 (by decide)
  · exact access.reads 7 (by decide)
  · exact access.firstStore
  · exact access.lastRead
  · exact access.stores 1 (by decide)
  · exact access.stores 8 (by decide)
  · exact access.stores 2 (by decide)
  · exact access.stores 3 (by decide)
  · exact access.stores 4 (by decide)
  · exact access.stores 5 (by decide)
  · exact access.stores 6 (by decide)
  · exact access.stores 7 (by decide)

private theorem termFacts (dst src r : BitVec 64) (n i : Nat) (m : Mem) (more : Bool)
    (guard : guardB bop.BLT 64#64
      ((dst + BitVec.ofNat 64 (8*(n/8))) -
        ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12))) = more) :
    TermFactsO (runGM body (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i))) (block more).term := by
  cases more <;> exact guard

private theorem blockFacts (dst src r : BitVec 64) (n i : Nat) (m : Mem)
    (loaded : Code.MemcpyLoaded m) (access : BulkAccess dst src i m) (more : Bool)
    (guard : guardB bop.BLT 64#64
      ((dst + BitVec.ofNat 64 (8*(n/8))) -
        ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12))) = more) :
    BBlockFacts m m (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)) (block more) := by
  have prog := bodyFacts dst src r n i m loaded access
  have term := termFacts dst src r n i m more guard
  cases more <;> refine ⟨prog, ?_, term⟩ <;>
    chain_facts loaded with "Vsa.Sim.Code.memcpy_at_"

private theorem bulkFacts_false (dst src r : BitVec 64) (n i : Nat) (m : Mem)
    (loaded : Code.MemcpyLoaded m) (access : BulkAccess dst src i m)
    (guard : guardB bop.BLT 64#64
      ((dst + BitVec.ofNat 64 (8*(n/8))) -
        ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12))) = false) :
    ChainFacts m m (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)) (bulkSeg false) := by
  change BBlockFacts m m (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)) (block false) ∧ _
  refine ⟨blockFacts dst src r n i m loaded access false guard, ?_⟩
  chain_facts loaded with "Vsa.Sim.Code.memcpy_at_"

private theorem bulkFacts_true (dst src r : BitVec 64) (n i : Nat) (m : Mem)
    (loaded : Code.MemcpyLoaded m) (access : BulkAccess dst src i m)
    (guard : guardB bop.BLT 64#64
      ((dst + BitVec.ofNat 64 (8*(n/8))) -
        ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12))) = true) :
    ChainFacts m m (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)) (bulkSeg true) := by
  change BBlockFacts m m (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)) (block true) ∧ _
  refine ⟨blockFacts dst src r n i m loaded access true guard, ?_⟩
  chain_facts loaded with "Vsa.Sim.Code.memcpy_at_"

/-- The actual bulk body and selected exit consume the owned access facts. -/
theorem bulkFacts {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before)
    (remaining : i+72 ≤ 8*(n/8)) (more : Bool)
    (guard : guardB bop.BLT 64#64
      ((dst + BitVec.ofNat 64 (8*(n/8))) -
        ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12))) = more) :
    ChainFacts before.σ.mem before.σ.mem (bulkRegs dst src r n i)
      (bulkLoads before.σ.mem (src.toNat + i)) (bulkSeg more) := by
  have access := bulkAccess h remaining
  cases more
  · exact bulkFacts_false dst src r n i before.σ.mem h.loaded access guard
  · exact bulkFacts_true dst src r n i before.σ.mem h.loaded access guard

#print axioms bulkFacts

end Vsa.Sim.MemcpyCopy

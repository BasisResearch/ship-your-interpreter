import Vsa.Sim.EnvDefineAppendStoreRun
import Vsa.Sim.rows.EnvDefineGrowLane

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Supply the append stores from the actual owned name-copy return. -/
theorem envDefineAppendInput_of_owned
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {target : Addr} {name : String} {v : Value}
    {esp env namePtr src copied r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {exts extsAfter : List Extent} {cap names vals : Nat} {before : Config}
    (F : EnvDefineMissFacts g N A SL phiF phiC st target name v esp env namePtr src r
      m exts before.σ.mem cap)
    (R : EnvDefineMissRegs g A SL st target esp env namePtr src r out M extsAfter before.σ.mem F.env_lt before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (geometry : EnvDefineGrowGeometry A SL esp src)
    (sourceAlign : src.toNat % 8 = 0)
    (pc : before.σ.regs.get? Register.PC = some 0x80002b44#64)
    (copyReg : before.σ.regs.get? Register.x9 = some copied)
    (copiedName : CString before.σ.mem copied.toNat name)
    (fresh : ∀ e ∈ exts, ExtDisjoint (copied.toNat, name.length + 1) e)
    (namesRead : read64 before.σ.mem (phiF target + 8) = some names)
    (valuesRead : read64 before.σ.mem (phiF target + 16) = some vals)
    (room : (st.store.frames[target]'F.env_lt).vars.length < cap) :
    EnvDefineAppendStoreInput (envDefineSaved g r) N A phiF phiC env src copied (esp - 64#64)
      (st.store.frames[target]'F.env_lt).parent (st.store.frames[target]'F.env_lt).vars name v cap names vals before := by
  obtain ⟨alloc, shared, readable, writes, heap, _, value, _⟩ := F.owned
  have capSigned := (heap.store.frames target F.env_lt).capSigned heap.ledger F.cap_read L.arena_ram.2
  have stackLo := geometry.stack.1
  have stackHi := geometry.stack.2.1
  have sourceLo := geometry.slot_above
  have sourceHi := geometry.slot_in_stack
  have ram := geometry.stack_ram
  have win := geometry.stack_win
  have sp64 := sp_sub64_toNat esp (by omega)
  obtain ⟨storeGeometry, namesArena, valuesArena, countArena⟩ := appendStoreFactsGeom_at heap F.env_lt
    F.env_addr F.cap_read namesRead valuesRead room capSigned
    (F.names_align names namesRead) (F.vals_align vals valuesRead)
    (F.store.frames_arena target F.env_lt).2 L.arena_ram L.arena_htif
    (by omega) (by omega) (by omega) sourceAlign
  refine
    { good := R.good, tick := R.tick, pc := pc, spReg := R.sp
      regs := ⟨R.s4, R.s5, copyReg, trivial⟩, savedSpills := R.saved
      code := F.text.Env_defineLoaded
      frame := ?_, capRead := ?_, namesRead := ?_, valuesRead := ?_
      room := room, word := F.word, copiedName := copiedName, footprint := ?_
      geometry := storeGeometry, namesArena := namesArena, valuesArena := valuesArena
      countArena := countArena, arenaStack := ?_, arenaCode := ?_ }
  · rw [F.env_addr]; exact F.store.frames target F.env_lt
  · rw [F.env_addr]; exact F.cap_read
  · rw [F.env_addr]; exact namesRead
  · rw [F.env_addr]; exact valuesRead
  · rw [F.env_addr]
    exact appendFootprint_of_owned heap F.env_lt F.cap_read namesRead valuesRead room fresh
      (Nat.le_refl _) value
  · rw [sp64]
    have := L.arena_stack
    omega
  · have := geometry.arena_image
    omega

#print axioms envDefineAppendInput_of_owned

end Vsa.Sim

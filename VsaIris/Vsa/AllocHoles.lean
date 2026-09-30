import VsaIris.Vsa.AllocBase
import VsaIris.Vsa.MallocRunAll
import VsaIris.Vsa.FreeRunAll
import VsaIris.Vsa.ReallocRunAll

namespace VsaIris.VsaHeap

open VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

structure AllocSpecs (live : Nat → Prop) : Prop where
  counted : DlMallocChgImpl (vsaModel live) vsaLayoutP vsaRoomB vsaChg SpOKA mallocEntryBV gpV
    vsaClob vsaSaved allocHeadroom allocText
  uncounted : DlMallocImpl (vsaModel live) vsaLayoutP SpOKA mallocEntryBV freeEntryBV gpV vsaClob
    vsaSaved allocHeadroom allocText
  freeCounted : DlFreeRoomImpl (vsaModel live) vsaLayoutP vsaRoomB vsaRoomB SpOKA freeEntryBV gpV
    vsaClob vsaSaved allocHeadroom allocText
  reallocUncounted : DlReallocImpl (vsaModel live) vsaLayoutP SpOKA reallocEntryBV gpV vsaClob
    vsaSaved allocHeadroom allocText

theorem allocSpecs (live : Nat → Prop) (hl : AllocLive live) :
    AllocSpecs live where
  counted := dlMallocChgImpl_of_run (mallocChgRun_proved live hl) shapeLocal_vsaLayoutP
    roomLocal_vsaRoomB vsaAllocRegs_nodup
  uncounted := dlMallocImpl_of_localRuns (mallocLocalRun_proved live hl) (freeLocalRun_proved live hl)
    shapeLocal_vsaLayoutP vsaAllocRegs_nodup
  freeCounted := dlFreeRoomImpl_of_run (freeChgRun_proved live hl) shapeLocal_vsaLayoutP
    roomLocal_vsaRoomB vsaAllocRegs_nodup
  reallocUncounted := dlReallocImpl_of_localRun (reallocLocalRun_proved live hl) shapeLocal_vsaLayoutP
    vsaAllocRegs_nodup (by decide)

end VsaIris.VsaHeap

import VsaIris.Vsa.MallocConsumer
import VsaIris.Vsa.ControlEnd

/-! Axiom audit for the iris-heap results: every headline theorem, printed. -/

#print axioms VsaIris.VsaHeap.BlockHeapAt.transport
#print axioms VsaIris.VsaHeap.imgShape_iff
#print axioms VsaIris.VsaHeap.blockHeapAt_of_heapAt
#print axioms VsaIris.VsaHeap.blockHeap_of_initial
#print axioms VsaIris.VsaHeap.Control.control_shape
#print axioms VsaIris.VsaHeap.Control.live_relative_frame_admits_both
#print axioms VsaIris.wp_localRun
#print axioms VsaIris.segFrom_of_runFact
#print axioms VsaIris.allocCall_of_localRun
#print axioms VsaIris.mallocSpec_of_localRun
#print axioms VsaIris.freeSpec_of_localRun
#print axioms VsaIris.dlMallocImpl_of_localRuns
#print axioms VsaIris.mallocRoomSpec_of_run
#print axioms VsaIris.dlMallocRoomImpl_of_run
#print axioms VsaIris.VsaHeap.vsaDlMallocImpl
#print axioms VsaIris.VsaHeap.vsaDlMallocRoomImpl
#print axioms VsaIris.VsaHeap.shape_iff_state
#print axioms VsaIris.VsaHeap.reserve_of_room
#print axioms VsaIris.wp_call_malloc_owns
#print axioms VsaIris.ownSet_agree_state
#print axioms VsaIris.VsaHeap.mallocCallerFacts_of_iris
#print axioms VsaIris.VsaHeap.mallocRoomCallerFacts_of_iris
#print axioms VsaIris.VsaHeap.Control.malloc64_end
#print axioms VsaIris.VsaHeap.Control.malloc64_roomEnd

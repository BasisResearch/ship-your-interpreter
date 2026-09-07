import Vsa.Sim.Code.Setjmp
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText_setjmpChunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : setjmpChunk0 mem := by
  exact ⟨h 28668 (by decide),
    h 28669 (by decide),
    h 28670 (by decide),
    h 28671 (by decide),
    h 28672 (by decide),
    h 28673 (by decide),
    h 28674 (by decide),
    h 28675 (by decide),
    h 28676 (by decide),
    h 28677 (by decide),
    h 28678 (by decide),
    h 28679 (by decide),
    h 28680 (by decide),
    h 28681 (by decide),
    h 28682 (by decide),
    h 28683 (by decide),
    h 28684 (by decide),
    h 28685 (by decide),
    h 28686 (by decide),
    h 28687 (by decide),
    h 28688 (by decide),
    h 28689 (by decide),
    h 28690 (by decide),
    h 28691 (by decide),
    h 28692 (by decide),
    h 28693 (by decide),
    h 28694 (by decide),
    h 28695 (by decide),
    h 28696 (by decide),
    h 28697 (by decide),
    h 28698 (by decide),
    h 28699 (by decide),
    h 28700 (by decide),
    h 28701 (by decide),
    h 28702 (by decide),
    h 28703 (by decide),
    h 28704 (by decide),
    h 28705 (by decide),
    h 28706 (by decide),
    h 28707 (by decide),
    h 28708 (by decide),
    h 28709 (by decide),
    h 28710 (by decide),
    h 28711 (by decide),
    h 28712 (by decide),
    h 28713 (by decide),
    h 28714 (by decide),
    h 28715 (by decide),
    h 28716 (by decide),
    h 28717 (by decide),
    h 28718 (by decide),
    h 28719 (by decide),
    h 28720 (by decide),
    h 28721 (by decide),
    h 28722 (by decide),
    h 28723 (by decide),
    h 28724 (by decide),
    h 28725 (by decide),
    h 28726 (by decide),
    h 28727 (by decide),
    h 28728 (by decide),
    h 28729 (by decide),
    h 28730 (by decide),
    h 28731 (by decide)⟩

theorem FixedTextLoaded.SetjmpLoaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : SetjmpLoaded mem :=
  fixedText_setjmpChunk0 h

#print axioms FixedTextLoaded.SetjmpLoaded

end Vsa.Sim.Code

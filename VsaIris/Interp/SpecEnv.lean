import VsaIris.Interp.Store
import VsaIris.Vsa.AllocHoles
import VsaIris.CallAbort
import VsaIris.Vsa.ImpureText

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

def envNewPC : BitVec 64 := 0x800029fc#64
def envDefinePC : BitVec 64 := 0x80002a5c#64
def envGetPC : BitVec 64 := 0x80002c10#64
def envSetPC : BitVec 64 := 0x80002cdc#64
def strcmpPC : BitVec 64 := 0x80006ea0#64
def strlenPC : BitVec 64 := 0x80006cf0#64
def memcpyPC : BitVec 64 := 0x80006bc8#64

def argClob : List Nat := [5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31]

def retClob : List Nat := 11 :: 12 :: argClob

def newSaved : List Nat := [8, 9, 18, 19, 20, 21, 22]
def getSaved : List Nat := [8, 9, 18, 19, 20, 21, 22]
def defineSaved : List Nat := [8, 9, 18, 19, 20, 21, 22]

def envNewNeed : Nat := 16 + allocHeadroom
def envGetNeed : Nat := 64
def envDefineNeed : Nat := 64 + allocHeadroom

structure EnvSp (s : BitVec 64) (need : Nat) : Prop where
  lo : htifLo + 16 + need ≤ s.toNat
  hi : s.toNat ≤ 0x100000000
  align : s.toNat % 16 = 0

structure SlotWin (a : Nat) : Prop where
  lo : 0x80000000 ≤ a
  hi : a + 24 ≤ 0x100000000
  htif : htifLo + 16 ≤ a
  align : a % 8 = 0

structure RamWin (a n : Nat) : Prop where
  lo : 0x80000000 ≤ a
  hi : a + n ≤ 0x100000000
  htif : a + n ≤ htifLo ∨ htifLo + 16 ≤ a

def Regime.plus : Regime → Nat → Regime
  | .counted k, c => .counted (k + c)
  | .uncounted, _ => .uncounted

@[simp] theorem Regime.plus_counted (k c : Nat) : (Regime.counted k).plus c = .counted (k + c) :=
  rfl
@[simp] theorem Regime.plus_uncounted (c : Nat) : Regime.uncounted.plus c = .uncounted := rfl

section Store

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

def heapStore (N : NativeAddrs) (ρ : Regime) (s : Store) : IProp GF :=
  iprop(∃ H B, heapRes vsaLayoutP vsaRoomB ρ H ∗ storeRepr N s B ∗ ⌜∀ b ∈ B, b ∈ H⌝)

theorem world_heapStore (N : NativeAddrs) (inp : Nat) (ρ : Regime) (st : St) (d : Nat) :
    world (GF := GF) N vsaLayoutP vsaRoomB inp ρ st d ⊣⊢
      heapStore N ρ st.store ∗ consoleOwn st.out ∗ Stdio.stdioOwn ∗ interpCtx inp d ∗
        Newlib.binImg := by
  unfold world worldE heapStore interpCtx
  constructor
  · iintro ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hb⟩
    iframe Hc Hio Hi Hb
    iexists H, B
    iframe Hh Hs %hB
  · iintro ⟨⟨%H, %B, Hh, Hs, %hB⟩, Hc, Hio, Hi, #Hb⟩
    iexists H, B
    iframe Hh Hs Hc Hio Hi %hB Hb

theorem world_store (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (ρ : Regime)
    (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢
      ∃ B, storeRepr N st.store B ∗ (storeRepr N st.store B -∗ world N L Room inp ρ st d) := by
  unfold world worldE
  iintro ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hb⟩
  iexists B
  iframe Hs
  iintro Hs
  iexists H, B
  iframe Hh Hs Hc Hio Hi %hB Hb

def getOut (N : NativeAddrs) (s : Store) (fa : Addr) (x : String) (out res : BitVec 64) :
    IProp GF :=
  match s.get? fa x with
  | some v => iprop(⌜res = 1#64⌝ ∗ valAt N out.toNat v)
  | none => iprop(⌜res = 0#64⌝ ∗ slot24 out.toNat)

def setOut (N : NativeAddrs) (s : Store) (B : List (Nat × Nat)) (fa : Addr) (x : String)
    (v : Value) (res : BitVec 64) : IProp GF :=
  match s.set? fa x v with
  | some s' => iprop(⌜res = 1#64⌝ ∗ storeRepr N s' B)
  | none => iprop(⌜res = 0#64⌝ ∗ storeRepr N s B)

def oomAt (pc sp0 s : BitVec 64) (need : Nat) (regs : List Nat) : IProp GF :=
  iprop(PC ↦ᵣ pc ∗ sp ↦ᵣ sp0 ∗ clobbered regs ∗ stackScratch s need ∗
    ∃ H, heapRes vsaLayoutP vsaRoomB .uncounted H)

variable {M : MachineModel}

def strcmpSpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (p q : BitVec 64) (x y : String), fnSpecW Wp strcmpPC
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ p ∗ (11 : Nat) ↦ᵣ q ∗
      clobbered (12 :: argClob) ∗ strAt p.toNat x ∗ strAt q.toNat y))
    (fun _ => iprop(∃ res : BitVec 64, (10 : Nat) ↦ᵣ res ∗ ⌜res = 0#64 ↔ x = y⌝ ∗
      clobbered retClob)))

def strlenSpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (p : BitVec 64) (x : String), fnSpecW Wp strlenPC
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ p ∗ clobbered retClob ∗ strAt p.toNat x))
    (fun _ => iprop((10 : Nat) ↦ᵣ BitVec.ofNat 64 x.length ∗ clobbered retClob)))

def memcpySpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (dst src : BitVec 64) (n : Nat) (img : Nat → BitVec 8), fnSpecW Wp memcpyPC
    (fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin dst.toNat n ∧ htifLo + 16 ≤ dst.toNat ∧
        RamWin src.toNat n⌝ ∗
      (10 : Nat) ↦ᵣ dst ∗ (11 : Nat) ↦ᵣ src ∗ (12 : Nat) ↦ᵣ BitVec.ofNat 64 n ∗
      clobbered argClob ∗ blockOwn dst.toNat n ∗ roImg (InExt (src.toNat, n)) img))
    (fun _ => iprop((10 : Nat) ↦ᵣ dst ∗ clobbered retClob ∗
      ownImg (InExt (dst.toNat, n)) (fun a => img (a - dst.toNat + src.toNat)))))

instance (Wp : MachWP (GF := GF) M) : Persistent (strcmpSpec Wp) := by
  unfold strcmpSpec; infer_instance
instance (Wp : MachWP (GF := GF) M) : Persistent (strlenSpec Wp) := by
  unfold strlenSpec; infer_instance
instance (Wp : MachWP (GF := GF) M) : Persistent (memcpySpec Wp) := by
  unfold memcpySpec; infer_instance

def envNewSpec (Wp : MachWP (GF := GF) M) (N : NativeAddrs) : IProp GF :=
  iprop(□ ∀ (ρ : Regime) (st : Store) (po : Option Addr) (par s : BitVec 64)
      (saved : List (Nat × BitVec 64)), ⌜saved.map Prod.fst = newSaved⌝ →
    fnSpecAbort Wp envNewPC
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp s envNewNeed⌝ ∗ (10 : Nat) ↦ᵣ par ∗ sp ↦ᵣ s ∗
        gp ↦ᵣ□ gpV ∗ codeX ∗ clobbered retClob ∗ savedOwn saved ∗ stackScratch s envNewNeed ∗
        parentAt po par.toNat ∗ heapStore N (ρ.plus envBytes) st))
      (fun _ => iprop(∃ e : BitVec 64, (10 : Nat) ↦ᵣ e ∗ sp ↦ᵣ s ∗ clobbered retClob ∗
        savedOwn saved ∗ stackScratch s envNewNeed ∗ heapStore N ρ (st.allocFrame po).1 ∗
        frameAt st.frames.size e.toNat))
      (iprop(⌜ρ = .uncounted⌝ ∗ oomAt 0x80002a38#64 (s - 16#64) s envNewNeed
        (VsaIris.ra :: 10 :: retClob ++ newSaved))))

def envGetSpec (Wp : MachWP (GF := GF) M) (N : NativeAddrs) : IProp GF :=
  iprop(□ ∀ (st : Store) (B : List (Nat × Nat)) (fa : Addr) (x : String) (e pn out s : BitVec 64)
      (saved : List (Nat × BitVec 64)), ⌜saved.map Prod.fst = getSaved⌝ →
    fnSpecW Wp envGetPC
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp s envGetNeed ∧ SlotWin out.toNat⌝ ∗
        (10 : Nat) ↦ᵣ e ∗ (11 : Nat) ↦ᵣ pn ∗ (12 : Nat) ↦ᵣ out ∗ sp ↦ᵣ s ∗
        clobbered argClob ∗ savedOwn saved ∗ stackScratch s envGetNeed ∗ frameAt fa e.toNat ∗
        strAt pn.toNat x ∗ slot24 out.toNat ∗ storeRepr N st B ∗ gp ↦ᵣ□ gpV ∗ codeX))
      (fun _ => iprop(∃ res : BitVec 64, (10 : Nat) ↦ᵣ res ∗ sp ↦ᵣ s ∗ clobbered retClob ∗
        savedOwn saved ∗ stackScratch s envGetNeed ∗ storeRepr N st B ∗
        getOut N st fa x out res)))

def envSetSpec (Wp : MachWP (GF := GF) M) (N : NativeAddrs) : IProp GF :=
  iprop(□ ∀ (st : Store) (B : List (Nat × Nat)) (fa : Addr) (x : String) (v : Value)
      (e pn pv s : BitVec 64) (saved : List (Nat × BitVec 64)), ⌜saved.map Prod.fst = getSaved⌝ →
    fnSpecW Wp envSetPC
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp s envGetNeed ∧ SlotWin pv.toNat⌝ ∗
        (10 : Nat) ↦ᵣ e ∗ (11 : Nat) ↦ᵣ pn ∗ (12 : Nat) ↦ᵣ pv ∗ sp ↦ᵣ s ∗
        clobbered argClob ∗ savedOwn saved ∗ stackScratch s envGetNeed ∗ frameAt fa e.toNat ∗
        strAt pn.toNat x ∗ valAt N pv.toNat v ∗ storeRepr N st B ∗ gp ↦ᵣ□ gpV ∗ codeX))
      (fun _ => iprop(∃ res : BitVec 64, (10 : Nat) ↦ᵣ res ∗ sp ↦ᵣ s ∗ clobbered retClob ∗
        savedOwn saved ∗ stackScratch s envGetNeed ∗ valAt N pv.toNat v ∗
        setOut N st B fa x v res)))

def envDefineSpec (Wp : MachWP (GF := GF) M) (N : NativeAddrs) : IProp GF :=
  iprop(□ ∀ (ρ : Regime) (st : Store) (fa : Addr) (x : String) (v : Value)
      (e pn pv s : BitVec 64) (saved : List (Nat × BitVec 64)),
      ⌜saved.map Prod.fst = defineSaved⌝ →
    fnSpecAbort Wp envDefinePC
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp s envDefineNeed ∧ SlotWin pv.toNat⌝ ∗
        (10 : Nat) ↦ᵣ e ∗ (11 : Nat) ↦ᵣ pn ∗ (12 : Nat) ↦ᵣ pv ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpV ∗
        codeX ∗ clobbered argClob ∗ savedOwn saved ∗ stackScratch s envDefineNeed ∗ frameAt fa e.toNat ∗
        strAt pn.toNat x ∗ valAt N pv.toNat v ∗ heapStore N (ρ.plus (defineCost st fa x)) st))
      (fun _ => iprop(sp ↦ᵣ s ∗ clobbered (10 :: retClob) ∗ savedOwn saved ∗
        stackScratch s envDefineNeed ∗ valAt N pv.toNat v ∗ heapStore N ρ (st.define fa x v)))
      (iprop(⌜ρ = .uncounted⌝ ∗ oomAt 0x80002bd0#64 (s - 64#64) s envDefineNeed
        (VsaIris.ra :: 10 :: retClob ++ defineSaved) ∗ valAt N pv.toNat v)))

end Store

structure ReallocNullRegs (rv : Nat → BitVec 64) (r n s : BitVec 64)
    (saved : List (Nat × BitVec 64)) : Prop where
  entry : EntryRegs rv reallocEntryBV r 0#64 s saved
  a1 : rv a1 = n

def ReallocNullChgRun (M : MachineModel) : Prop :=
  ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (k c : Nat),
    saved.map Prod.fst = vsaSaved → vsaChg n.toNat c → SpOKA s → r.toNat % 4 = 0 →
    ReallocNullRegs rv r n s saved →
    vsaLayoutP.Shape mv H → vsaRoomB mv H (k + c) →
    (∀ a, stackWin s allocHeadroom a → ¬ heapFoot vsaLayoutP H a) →
    ∃ fuel, LocalRun M [(gp, gpV)] allocText (allocRegs vsaClob vsaSaved)
      (mallocBytes vsaLayoutP H s allocHeadroom)
      (MallocRoomEnd vsaLayoutP vsaRoomB H n r s saved k) fuel rv mv

def ReallocNullLocalRun (M : MachineModel) : Prop :=
  ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8),
    saved.map Prod.fst = vsaSaved → SpOKA s → r.toNat % 4 = 0 →
    ReallocNullRegs rv r n s saved →
    vsaLayoutP.Shape mv H → (∀ a, stackWin s allocHeadroom a → ¬ heapFoot vsaLayoutP H a) →
    ∃ fuel, LocalRun M [(gp, gpV)] allocText (allocRegs vsaClob vsaSaved)
      (mallocBytes vsaLayoutP H s allocHeadroom) (MallocEnd vsaLayoutP H n r s saved) fuel rv mv

end VsaIris.Interp

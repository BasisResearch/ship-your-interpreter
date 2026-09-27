import VsaIris.MallocRun
import VsaIris.Vsa.Stdio
import VsaIris.Vsa.BinDom
import Vsa.RuntimeRepr
import Vsa.MemReprWithin
import Vsa.While.StackNeed
import Vsa.Sim.StoreInvariant

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

def imgLE (img : Nat → BitVec 8) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (img a).toNat + 256 * imgLE img (a + 1) n

def imgW (img : Nat → BitVec 8) (a : Nat) : BitVec 64 := BitVec.ofNat 64 (imgLE img a 8)

def ImgAgree (S : Nat → Prop) (img : Nat → BitVec 8) (m : Mem) : Prop :=
  ∀ a, S a → m[a]? = some (img a)

theorem imgLE_congr {img img' : Nat → BitVec 8} {a : Nat} :
    ∀ {n : Nat}, (∀ i, i < n → img (a + i) = img' (a + i)) → imgLE img a n = imgLE img' a n
  | 0, _ => rfl
  | n + 1, h => by
    unfold imgLE
    rw [show img a = img' a by simpa using h 0 (by omega),
      imgLE_congr (a := a + 1) (n := n) (fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using h (i + 1) (by omega))]

theorem imgW_agree {f g : Nat → BitVec 8} {a : Nat} (h : ∀ j, j < 8 → f (a + j) = g (a + j)) :
    imgW f a = imgW g a := by
  unfold imgW; rw [imgLE_congr h]

theorem readLE_of_img {img : Nat → BitVec 8} {m : Mem} {a : Nat} :
    ∀ {n : Nat}, (∀ i, i < n → m[a + i]? = some (img (a + i))) → readLE m a n = some (imgLE img a n)
  | 0, _ => rfl
  | n + 1, h => by
    have h0 : m[a]? = some (img a) := by simpa using h 0 (by omega)
    have ht := readLE_of_img (img := img) (m := m) (a := a + 1) (n := n) (fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using h (i + 1) (by omega))
    simp [readLE, h0, ht, imgLE]

theorem imgLE_lt (img : Nat → BitVec 8) (a : Nat) : ∀ n, imgLE img a n < 256 ^ n
  | 0 => by simp [imgLE]
  | n + 1 => by
    have := imgLE_lt img (a + 1) n
    have hb := (img a).isLt
    simp only [imgLE, Nat.pow_succ]
    omega

theorem imgW_toNat (img : Nat → BitVec 8) (a : Nat) : (imgW img a).toNat = imgLE img a 8 := by
  unfold imgW
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using imgLE_lt img a 8)]

section Bytes

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

abbrev ownImg (S : Nat → Prop) (img : Nat → BitVec 8) : IProp GF :=
  ownSet S (fun a => a ↦ₘ img a)

def roOn (P : Nat → Prop) (m : Mem) : IProp GF :=
  iprop(□ ∀ (k : Nat) (b : BitVec 8), ⌜P k⌝ → ⌜m[k]? = some b⌝ → k ↦ₘ□ b)

instance (P : Nat → Prop) (m : Mem) : Persistent (roOn (GF := GF) P m) := by
  unfold roOn; infer_instance

theorem roOn_mono {P Q : Nat → Prop} {m : Mem} (h : ∀ k, P k → Q k) :
    roOn (GF := GF) Q m ⊢ roOn P m := by
  unfold roOn
  iintro #H
  imodintro
  iintro %k %b %hk %hb
  iapply H $$ %k %b %(h k hk) %hb

theorem roOn_byte {P : Nat → Prop} {m : Mem} {k : Nat} {b : BitVec 8} (hk : P k)
    (hb : m[k]? = some b) : roOn (GF := GF) P m ⊢ k ↦ₘ□ b := by
  unfold roOn
  iintro #H
  iapply H $$ %k %b %hk %hb

theorem memRO_excl_ne (a a' : Nat) (b b' : BitVec 8) :
    (a ↦ₘ□ b) ∗ (a' ↦ₘ b') ⊢@{IProp GF} ⌜a ≠ a'⌝ := by
  unfold memPointsTo
  iintro ⟨H1, H2⟩
  ihave %h := ghost_map_elem_ne _ _ _ _ _ _ $$ H2 H1
  ipureintro
  exact Ne.symm h

end Bytes

class InterpGS (GF : BundledGFunctors) where
  frameName : GName
  closName : GName

section Repr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

def frameAt (fa e : Nat) : IProp GF := ghost_map_elem I.frameName DFrac.discard fa e

def closAt (ca p : Nat) : IProp GF := ghost_map_elem I.closName DFrac.discard ca p

instance (fa e : Nat) : Persistent (frameAt (GF := GF) fa e) := by unfold frameAt; infer_instance
instance (ca p : Nat) : Persistent (closAt (GF := GF) ca p) := by unfold closAt; infer_instance

theorem frameAt_agree (fa e e' : Nat) : frameAt (GF := GF) fa e ∗ frameAt fa e' ⊢ ⌜e = e'⌝ := by
  unfold frameAt; exact ghost_map_elem_agree _ _ _ _ _ _
theorem closAt_agree (ca p p' : Nat) : closAt (GF := GF) ca p ∗ closAt ca p' ⊢ ⌜p = p'⌝ := by
  unfold closAt; exact ghost_map_elem_agree _ _ _ _ _ _

def _root_.VsaIris.Newlib.binImg : IProp GF :=
  iprop(roImg Newlib.textDom Newlib.textByte ∗ roImg Newlib.rodataDom Newlib.rodataByte)

instance : Persistent (Newlib.binImg (GF := GF)) := by unfold Newlib.binImg; infer_instance

def CStrImg (img : Nat → BitVec 8) (p : Nat) (s : String) : Prop :=
  (∀ i (h : i < s.toList.length), img (p + i) = BitVec.ofNat 8 (s.toList[i]).toNat ∧
      0 < (s.toList[i]).toNat ∧ (s.toList[i]).toNat < 128) ∧
    img (p + s.toList.length) = 0

def htifLo : Nat := 0x8001ad00

structure StrWin (p len : Nat) : Prop where
  lo : 0x80000000 ≤ p
  hi : p + len + 8 ≤ 0x88000000
  htif : p + len + 8 ≤ htifLo ∨ htifLo + 16 ≤ p

def strAt (p : Nat) (s : String) : IProp GF :=
  iprop(∃ img, ⌜CStrImg img p s ∧ StrWin p s.toList.length⌝ ∗
    roImg (InExt (p, s.toList.length + 1)) img)

instance (p : Nat) (s : String) : Persistent (strAt (GF := GF) p s) := by
  unfold strAt; infer_instance

def astSs (a n : Nat) (ss : List Stmt) : IProp GF :=
  iprop(∃ (P : Nat → Prop) (m : Mem), ⌜StmtArrayReprWithin m P a n ss⌝ ∗ roOn P m)

structure ReadOK (k : Nat) : Prop where
  lo : 0x80000000 ≤ k
  hi : k < 0x100000000
  off : k < Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ k
  win : k + 8 ≤ 0x88000000 ∧ (k + 8 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ k)

def astEG (a : Nat) (e : Expr) : IProp GF :=
  iprop(∃ (P : Nat → Prop) (m : Mem), ⌜ExprReprWithin m P a e ∧ ∀ k, P k → ReadOK k⌝ ∗ roOn P m)

instance (a : Nat) (e : Expr) : Persistent (astEG (GF := GF) a e) := by
  unfold astEG; infer_instance

omit I in

def valOf (N : NativeAddrs) : Value → BitVec 64 → BitVec 64 → BitVec 64 → IProp GF
  | .null, w0, _, _ => iprop(⌜w0.toNat % 2^32 = 0⌝)
  | .bool b, w0, w1, _ => iprop(⌜w0.toNat % 2^32 = 1 ∧ w1.toNat % 2^32 = cond b 1 0⌝)
  | .int n, w0, w1, _ => iprop(⌜w0.toNat % 2^32 = 2 ∧ w1.toInt = n⌝)
  | .str s, w0, w1, _ => iprop(⌜w0.toNat % 2^32 = 3 ∧ w1.toNat ≠ 0⌝ ∗ strAt w1.toNat s)
  | .closure ca, w0, w1, _ => iprop(⌜w0.toNat % 2^32 = 4 ∧ w1.toNat ≠ 0⌝ ∗ closAt ca w1.toNat)
  | .native f, w0, w1, w2 =>
      iprop(⌜w0.toNat % 2^32 = 5 ∧ w2.toNat = N.addr f⌝ ∗ strAt w1.toNat (nativeName f))

instance (N : NativeAddrs) (v : Value) (w0 w1 w2 : BitVec 64) :
    Persistent (valOf (GF := GF) N v w0 w1 w2) := by
  cases v <;> unfold valOf <;> infer_instance

abbrev valImg (N : NativeAddrs) (img : Nat → BitVec 8) (a : Nat) (v : Value) : IProp GF :=
  valOf N v (imgW img a) (imgW img (a + 8)) (imgW img (a + 16))

def slot24 (a : Nat) : IProp GF := blockOwn a 24

def valAt (N : NativeAddrs) (a : Nat) (v : Value) : IProp GF :=
  iprop(∃ img, ownImg (InExt (a, 24)) img ∗ valImg N img a v)

theorem valAt_slot (N : NativeAddrs) (a : Nat) (v : Value) :
    valAt (GF := GF) N a v ⊢ slot24 a := by
  unfold valAt slot24 blockOwn
  iintro ⟨%img, H, -⟩
  iapply ownSet_forget $$ H

structure ClosObj (img : Nat → BitVec 8) (p q e : Nat) : Prop where
  p_ne : p ≠ 0
  e_ne : e ≠ 0
  fn : imgLE img p 8 = q
  env : imgLE img (p + 8) 8 = e
  objOK : ∀ k, InExt (p, 16) k → ReadOK k

def closOwn (ca : Nat) (cd : ClosureData) : IProp GF :=
  iprop(∃ (p q e : Nat) (img : Nat → BitVec 8), closAt ca p ∗ ⌜ClosObj img p q e⌝ ∗
    roImg (InExt (p, 16)) img ∗ astEG q (.fn cd.name cd.params cd.body) ∗ frameAt cd.env e)

instance (ca : Nat) (cd : ClosureData) : Persistent (closOwn (GF := GF) ca cd) := by
  unfold closOwn; infer_instance

structure FrameGeom where
  e : Nat
  cap : Nat
  pn : Nat
  pv : Nat
  par : Nat
  sblk : Nat × Nat
  nblk : Nat × Nat
  vblk : Nat × Nat

def FrameGeom.blocks (G : FrameGeom) : List (Nat × Nat) :=
  G.sblk :: (if G.cap = 0 then [] else [G.nblk, G.vblk])

def BlocksCover (bl : List (Nat × Nat)) (a : Nat) : Prop := ∃ b ∈ bl, InExt b a

def ExtDisj (b b' : Nat × Nat) : Prop := ∀ a, InExt b a → ¬ InExt b' a

structure BlockWin (b : Nat × Nat) : Prop where
  lo : 0x80000000 ≤ b.1
  hi : b.1 + b.2 ≤ 0x100000000
  htif : htifLo + 16 ≤ b.1
  align : b.1 % 16 = 0

def capForAux : (fuel cap k : Nat) → Nat
  | 0, cap, _ => cap
  | fuel + 1, cap, k => if k ≤ cap then cap else capForAux fuel (if cap = 0 then 8 else 2 * cap) k

def capFor (k : Nat) : Nat := capForAux k 0 k

structure FrameLayout (img : Nat → BitVec 8) (G : FrameGeom) (n : Nat) : Prop where
  e_ne : G.e ≠ 0
  sblk : G.sblk.1 ≤ G.e ∧ G.e + 32 ≤ G.sblk.1 + G.sblk.2
  count : imgLE img G.e 4 = n
  cap : imgLE img (G.e + 4) 4 = G.cap
  names : imgLE img (G.e + 8) 8 = G.pn
  vals : imgLE img (G.e + 16) 8 = G.pv
  parent : imgLE img (G.e + 24) 8 = G.par
  count_le : n ≤ G.cap
  empty : G.cap = 0 → G.pn = 0 ∧ G.pv = 0
  arrays : 0 < G.cap → G.nblk = (G.pn, 8 * G.cap) ∧ G.vblk = (G.pv, 24 * G.cap)
  disjoint : G.blocks.Pairwise ExtDisj
  win : ∀ b ∈ G.blocks, BlockWin b
  e_align : G.e % 8 = 0
  cap_canon : G.cap = capFor n

theorem FrameLayout.arrays_le {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) (hc : 0 < G.cap) :
    G.nblk.1 = G.pn ∧ 8 * G.cap ≤ G.nblk.2 ∧ G.vblk.1 = G.pv ∧ 24 * G.cap ≤ G.vblk.2 := by
  obtain ⟨h1, h2⟩ := h.arrays hc
  rw [h1, h2]; exact ⟨rfl, Nat.le_refl _, rfl, Nat.le_refl _⟩

def bindings (N : NativeAddrs) (img : Nat → BitVec 8) (pn pv : Nat)
    (vars : List (String × Value)) : IProp GF :=
  sepL vars.zipIdx (fun p =>
    iprop(strAt (imgLE img (pn + 8 * p.2) 8) p.1.1 ∗ valImg N img (pv + 24 * p.2) p.1.2))

instance (N : NativeAddrs) (img : Nat → BitVec 8) (pn pv : Nat) (vars : List (String × Value)) :
    Persistent (bindings (GF := GF) N img pn pv vars) := by
  unfold bindings; infer_instance

def parentAt : Option Addr → Nat → IProp GF
  | none, par => iprop(⌜par = 0⌝)
  | some pa, par => iprop(⌜par ≠ 0⌝ ∗ frameAt pa par)

instance (o : Option Addr) (par : Nat) : Persistent (parentAt (GF := GF) o par) := by
  cases o <;> unfold parentAt <;> infer_instance

def frameBody (N : NativeAddrs) (f : Frame) (G : FrameGeom) : IProp GF :=
  iprop(∃ img, ⌜FrameLayout img G f.vars.length⌝ ∗ ownImg (BlocksCover G.blocks) img ∗
    bindings N img G.pn G.pv f.vars ∗ parentAt f.parent G.par)

def frameOwn (N : NativeAddrs) (fa : Addr) (f : Frame) (bl : List (Nat × Nat)) : IProp GF :=
  iprop(∃ G : FrameGeom, ⌜bl = G.blocks⌝ ∗ frameAt fa G.e ∗ frameBody N f G)

def framesOwn (N : NativeAddrs) : Nat → List Frame → List (List (Nat × Nat)) → IProp GF
  | _, [], [] => iprop(emp)
  | i, f :: fs, bl :: Bs => iprop(frameOwn N i f bl ∗ framesOwn N (i + 1) fs Bs)
  | _, _, _ => iprop(False)

@[simp] theorem framesOwn_nil (N : NativeAddrs) (i : Nat) :
    framesOwn (GF := GF) N i [] [] = iprop(emp) := rfl
@[simp] theorem framesOwn_cons (N : NativeAddrs) (i : Nat) (f : Frame) (fs : List Frame)
    (bl : List (Nat × Nat)) (Bs : List (List (Nat × Nat))) :
    framesOwn (GF := GF) N i (f :: fs) (bl :: Bs) = iprop(frameOwn N i f bl ∗ framesOwn N (i + 1) fs Bs) :=
  rfl
theorem framesOwn_nil_cons (N : NativeAddrs) (i : Nat) (bl : List (Nat × Nat))
    (Bs : List (List (Nat × Nat))) : framesOwn (GF := GF) N i [] (bl :: Bs) = iprop(False) := rfl
theorem framesOwn_cons_nil (N : NativeAddrs) (i : Nat) (f : Frame) (fs : List Frame) :
    framesOwn (GF := GF) N i (f :: fs) [] = iprop(False) := rfl

def closuresOwn : Nat → List ClosureData → IProp GF
  | _, [] => iprop(emp)
  | i, cd :: cs => iprop(closOwn i cd ∗ closuresOwn (i + 1) cs)

@[simp] theorem closuresOwn_nil (i : Nat) : closuresOwn (GF := GF) i [] = iprop(emp) := rfl
@[simp] theorem closuresOwn_cons (i : Nat) (cd : ClosureData) (cs : List ClosureData) :
    closuresOwn (GF := GF) i (cd :: cs) = iprop(closOwn i cd ∗ closuresOwn (i + 1) cs) := rfl

instance (i : Nat) (cs : List ClosureData) : Persistent (closuresOwn (GF := GF) i cs) := by
  induction cs generalizing i with
  | nil => unfold closuresOwn; infer_instance
  | cons cd cs ih => unfold closuresOwn; infer_instance

structure StoreMaps (mf mc : NatMap Nat) (s : Store) : Prop where
  frames : ∀ k, (PartialMap.get? mf k).isSome ↔ k < s.frames.size
  closures : ∀ k, (PartialMap.get? mc k).isSome ↔ k < s.closures.size
  clos_inj : ∀ a b p, PartialMap.get? mc a = some p → PartialMap.get? mc b = some p → a = b

structure StorePure (mf mc : NatMap Nat) (s : Store) (B : List (Nat × Nat))
    (Bs : List (List (Nat × Nat))) : Prop where
  maps : StoreMaps mf mc s
  blocks : B = Bs.flatten
  bodies : StoreBodiesBound s perCallBudget
  inv : Vsa.Sim.StoreInvariant s

def storeRepr (N : NativeAddrs) (s : Store) (B : List (Nat × Nat)) : IProp GF :=
  iprop(∃ (mf mc : NatMap Nat) (Bs : List (List (Nat × Nat))),
    ghost_map_auth I.frameName (DFrac.own 1) mf ∗ ghost_map_auth I.closName (DFrac.own 1) mc ∗
    ⌜StorePure mf mc s B Bs⌝ ∗
    framesOwn N 0 s.frames.toList Bs ∗ closuresOwn 0 s.closures.toList)

def interpDepthOff : Nat := 8
def interpJmpOff : Nat := 16
def interpJmpLen : Nat := 208
def interpErrOff : Nat := 224
def interpErrLen : Nat := 256

def wordAt (a n v : Nat) : IProp GF :=
  iprop(∃ img, ownImg (InExt (a, n)) img ∗ ⌜imgLE img a n = v⌝)

def wordRO (a n v : Nat) : IProp GF :=
  iprop(∃ img, roImg (InExt (a, n)) img ∗ ⌜imgLE img a n = v⌝)

def errAny (inp : Nat) : IProp GF := blockOwn (inp + interpErrOff) interpErrLen

def errStr (inp : Nat) : IProp GF :=
  iprop(∃ img, ownImg (InExt (inp + interpErrOff, interpErrLen)) img ∗
    ⌜∃ k, k < interpErrLen ∧ img (inp + interpErrOff + k) = 0⌝)

def interpCoreE (inp d : Nat) (E : IProp GF) : IProp GF :=
  iprop(∃ g, wordRO inp 8 g ∗ frameAt 0 g ∗ wordAt (inp + interpDepthOff) 4 d ∗
    ⌜d ≤ Vsa.While.maxCallDepth⌝ ∗ blockOwn (inp + interpDepthOff + 4) 4 ∗ E)

def interpCore (inp d : Nat) : IProp GF := interpCoreE inp d (errAny inp)

def jmpRO (inp : Nat) (jb : Nat → BitVec 8) : IProp GF :=
  roImg (InExt (inp + interpJmpOff, interpJmpLen)) jb

instance (inp : Nat) (jb : Nat → BitVec 8) : Persistent (jmpRO (GF := GF) inp jb) := by
  unfold jmpRO; infer_instance

def interpCtxE (inp d : Nat) (E : IProp GF) : IProp GF :=
  iprop(interpCoreE inp d E ∗ ∃ jb, jmpRO inp jb ∗ ⌜(imgW jb (inp + interpJmpOff)).toNat % 4 = 0⌝)

def interpCtx (inp d : Nat) : IProp GF := interpCtxE inp d (errAny inp)

def interpCtxPre (inp d : Nat) : IProp GF :=
  iprop(interpCore inp d ∗ blockOwn (inp + interpJmpOff) interpJmpLen)

inductive Regime where
  | counted (k : Nat)
  | uncounted

def heapRes (L : DlLayout) (Room : RoomPred) : Regime → List (Nat × Nat) → IProp GF
  | .counted k, H => isHeapRoom L Room H k
  | .uncounted, H => isHeap L H

omit I in

def worldE (E : IProp GF) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (ρ : Regime) (st : St) (d : Nat) : IProp GF :=
  iprop(∃ H B, heapRes L Room ρ H ∗ storeRepr N st.store B ∗ consoleOwn st.out ∗
    Stdio.stdioOwn ∗ interpCtxE inp d E ∗ ⌜∀ b ∈ B, b ∈ H⌝ ∗ Newlib.binImg)

def world (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (ρ : Regime) (st : St) (d : Nat) : IProp GF :=
  worldE (errAny inp) N L Room inp ρ st d

theorem worldE_binImg (E : IProp GF) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (ρ : Regime) (st : St) (d : Nat) :
    worldE E N L Room inp ρ st d ⊢ worldE E N L Room inp ρ st d ∗ Newlib.binImg := by
  unfold worldE
  iintro ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hb⟩
  isplitl [Hh Hs Hc Hio Hi]
  · iexists H, B
    iframe Hh Hs Hc Hio Hi
    isplitr
    · ipureintro; exact hB
    · iexact Hb
  · iexact Hb

theorem world_binImg (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (ρ : Regime) (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢ world N L Room inp ρ st d ∗ Newlib.binImg :=
  worldE_binImg _ N L Room inp ρ st d

end Repr

end VsaIris.Interp

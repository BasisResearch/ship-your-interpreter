import VsaIris.Interp.Store

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

def memImg (m : Mem) : Nat → BitVec 8 := fun k => (m[k]?).getD 0

theorem memImg_eq {m : Mem} {k : Nat} {b : BitVec 8} (h : m[k]? = some b) :
    memImg m k = b := by simp [memImg, h]

theorem readLE_succ {m : Mem} {n a v : Nat} (h : readLE m a (n + 1) = some v) :
    ∃ b rest, m[a]? = some b ∧ readLE m (a + 1) n = some rest ∧ v = b.toNat + 256 * rest := by
  have h' : (m[a]?).bind
      (fun b => (readLE m (a + 1) n).bind (fun rest => some (b.toNat + 256 * rest))) = some v := h
  simp only [Option.bind_eq_some_iff] at h'
  obtain ⟨b, hb, rest, hr, hv⟩ := h'
  exact ⟨b, rest, hb, hr, (Option.some.inj hv).symm⟩

theorem readLE_mapped {m : Mem} : ∀ {n a v : Nat}, readLE m a n = some v →
    ∀ i, i < n → m[a + i]? = some (memImg m (a + i))
  | 0, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, a, v, h, i, hi => by
    obtain ⟨b, rest, hb, hrest, -⟩ := readLE_succ h
    match i with
    | 0 => simpa [memImg_eq hb] using hb
    | i + 1 =>
      have := readLE_mapped (m := m) (n := n) (a := a + 1) hrest i (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem readLE_memImg {m : Mem} : ∀ {n a v : Nat}, readLE m a n = some v →
    imgLE (memImg m) a n = v
  | 0, _, _, h => by simpa [imgLE] using Option.some.inj h
  | n + 1, a, v, h => by
    obtain ⟨b, rest, hb, hrest, hv⟩ := readLE_succ h
    rw [imgLE, memImg_eq hb, readLE_memImg (m := m) (n := n) (a := a + 1) hrest, hv]

theorem readLE_lt {m : Mem} : ∀ {n a v : Nat}, readLE m a n = some v → v < 256 ^ n
  | 0, _, _, h => by have := Option.some.inj h; simp; omega
  | n + 1, a, v, h => by
    obtain ⟨b, rest, -, hrest, hv⟩ := readLE_succ h
    have hb := b.isLt
    have := readLE_lt (m := m) (n := n) (a := a + 1) hrest
    simp only [Nat.pow_succ]
    omega

theorem imgLE_split (img : Nat → BitVec 8) (a : Nat) :
    ∀ n k, imgLE img a (n + k) = imgLE img a n + 256 ^ n * imgLE img (a + n) k
  | 0, k => by simp [imgLE]
  | n + 1, k => by
    have := imgLE_split img (a + 1) n k
    simp only [Nat.succ_add, imgLE, this, Nat.pow_succ,
      show a + 1 + n = a + (n + 1) by omega, Nat.mul_add, Nat.mul_left_comm,
      Nat.mul_assoc, Nat.add_assoc]

theorem imgW_lo32 (img : Nat → BitVec 8) (a : Nat) :
    (imgW img a).toNat % 2 ^ 32 = imgLE img a 4 := by
  have he : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  have hlt : imgLE img a 4 < 2 ^ 32 := by
    have := imgLE_lt img a 4; omega
  rw [imgW_toNat, show (8 : Nat) = 4 + 4 from rfl, imgLE_split, he,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem imgW_read64 {m : Mem} {a v : Nat} (h : read64 m a = some v) :
    (imgW (memImg m) a).toNat = v := by
  rw [imgW_toNat, readLE_memImg h]

section Bridge

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

omit I in

theorem roOn_of_roImg {P : Nat → Prop} {img : Nat → BitVec 8} {m : Mem}
    (h : ∀ k b, P k → m[k]? = some b → img k = b) : roImg (GF := GF) P img ⊢ roOn P m := by
  unfold roImg roOn
  iintro #H
  imodintro
  iintro %k %b %hk %hb
  rw [← h k b hk hb]
  iapply H $$ %k %hk

omit I in

theorem roOn_of_ownImg {P : Nat → Prop} {img : Nat → BitVec 8} {m : Mem}
    (h : ∀ k b, P k → m[k]? = some b → img k = b) :
    ownImg (GF := GF) P img ⊢ |==> roOn P m := by
  iintro H
  imod ownImg_persist P img $$ H with H
  imodintro
  iapply roOn_of_roImg h $$ H

omit I in

theorem roImg_of_roOn {P S : Nat → Prop} {m : Mem}
    (h : ∀ k, S k → P k ∧ ∃ b, m[k]? = some b) :
    roOn (GF := GF) P m ⊢ roImg S (memImg m) := by
  unfold roImg
  iintro #H
  imodintro
  iintro %k %hk
  obtain ⟨hP, b, hb⟩ := h k hk
  rw [memImg_eq hb]
  iapply roOn_byte hP hb $$ H

omit I in

theorem cstr_bytes {m : Mem} : ∀ {p : Nat} {cs : List Char}, CStr m p cs →
    (∀ i, i < cs.length → ∃ b : BitVec 8, m[p + i]? = some b ∧ b ≠ 0 ∧ b.toNat < 128 ∧
        cs[i]? = some (Char.ofNat b.toNat)) ∧ m[p + cs.length]? = some 0
  | p, _, .nil hz => ⟨fun i hi => absurd hi (by simp), by simpa using hz⟩
  | p, _, .cons (b := b) hb hne hascii ht => by
    obtain ⟨hi, hz⟩ := cstr_bytes ht
    refine ⟨fun i hi' => ?_, ?_⟩
    · match i with
      | 0 => exact ⟨b, by simpa using hb, hne, hascii, by simp⟩
      | i + 1 =>
        obtain ⟨b', hb', hne', hascii', hc'⟩ := hi i (by simpa using hi')
        exact ⟨b', by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hb', hne', hascii',
          by simpa using hc'⟩
    · simpa [Nat.add_assoc, Nat.add_comm 1 (List.length _)] using hz

theorem char_ofNat_toNat' (b : BitVec 8) (hb : b.toNat < 128) :
    (Char.ofNat b.toNat).toNat = b.toNat := by
  rw [Char.toNat, Char.ofNat,
    dif_pos (show b.toNat.isValidChar by left; show b.toNat < 55296; omega)]
  simp only [Char.ofNatAux, UInt32.toNat]
  rfl

omit I in

theorem cstrImg_of_cstring {m : Mem} {p : Nat} {s : String} (h : CString m p s) :
    CStrImg (memImg m) p s ∧ ∀ i, i ≤ s.toList.length → ∃ b : BitVec 8, m[p + i]? = some b := by
  obtain ⟨cs, hcs, rfl⟩ := h
  obtain ⟨hi, hz⟩ := cstr_bytes hcs
  have hlist : (String.ofList cs).toList = cs := String.toList_ofList
  refine ⟨⟨fun i hi' => ?_, ?_⟩, fun i hi' => ?_⟩
  · have hi'' : i < cs.length := by rw [hlist] at hi'; exact hi'
    obtain ⟨b, hb, hne, hascii, hc⟩ := hi i hi''
    have hget : cs[i] = Char.ofNat b.toNat := by
      have := hc; rw [List.getElem?_eq_getElem hi''] at this; exact Option.some.inj this
    have hcode : ((String.ofList cs).toList[i]'hi').toNat = b.toNat := by
      simp only [List.getElem_of_eq hlist hi', hget]
      exact char_ofNat_toNat' b hascii
    have hbne : 0 < b.toNat := by
      rcases Nat.eq_zero_or_pos b.toNat with h0 | h0
      · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h0) hne
      · exact h0
    refine ⟨?_, by omega, by omega⟩
    rw [memImg_eq hb, hcode]
    exact (by simp : BitVec.ofNat 8 b.toNat = b).symm
  · rw [hlist]; exact memImg_eq hz
  · rw [hlist] at hi'
    rcases Nat.lt_or_ge i cs.length with hlt | hge
    · obtain ⟨b, hb, -⟩ := hi i hlt; exact ⟨b, hb⟩
    · have : i = cs.length := by omega
      subst this; exact ⟨0, hz⟩

def SharedWin (P : Nat → Prop) : Prop :=
  ∀ k, P k → 0x80000000 ≤ k ∧ k + 8 ≤ 0x88000000 ∧ (k + 8 ≤ htifLo ∨ htifLo + 16 ≤ k)

theorem strWin_of_shared {P : Nat → Prop} {p len : Nat} (hw : SharedWin P)
    (hP : ∀ i, i ≤ len → P (p + i)) : StrWin p len := by
  obtain ⟨h0lo, -, h0⟩ := hw p (by simpa using hP 0 (by omega))
  obtain ⟨-, hnhi, hn⟩ := hw (p + len) (hP len (Nat.le_refl _))
  refine ⟨h0lo, by omega, ?_⟩
  rcases h0 with h0 | h0
  · rcases hn with hn | hn
    · left; exact hn
    · have hk := hw (p + (htifLo - p)) (hP _ (by omega))
      rw [show p + (htifLo - p) = htifLo by omega] at hk
      omega
  · right; exact h0

omit I in

theorem strAt_of_cstringWithin {P : Nat → Prop} {m : Mem} {p : Nat} {s : String}
    (h : CStringWithin m P p s) (hw : SharedWin P) : roOn (GF := GF) P m ⊢ strAt p s := by
  obtain ⟨hstr, hP⟩ := h
  obtain ⟨himg, hmap⟩ := cstrImg_of_cstring hstr
  unfold strAt
  iintro H
  iexists (memImg m)
  isplitr
  · ipureintro
    exact ⟨himg, strWin_of_shared hw fun i hi => hP i (by simpa [String.length] using hi)⟩
  iapply roImg_of_roOn (P := P) (S := InExt (p, s.toList.length + 1)) ?_ $$ H
  intro k hk
  obtain ⟨i, hi, rfl⟩ : ∃ i, i ≤ s.toList.length ∧ k = p + i := by
    unfold InExt at hk; exact ⟨k - p, by omega, by omega⟩
  exact ⟨hP i (by simpa [String.length] using hi), hmap i hi⟩

omit I in

omit I in

omit I in
theorem astSs_of_stmtArrayRepr {P : Nat → Prop} {m : Mem} {a n : Nat} {ss : List Stmt}
    (h : StmtArrayReprWithin m P a n ss) : roOn (GF := GF) P m ⊢ astSs a n ss := by
  unfold astSs
  iintro H
  iexists P, m
  iframe H %h

omit I in

theorem astSs_of_programRepr {P : Nat → Prop} {m : Mem} {a n : Nat} {p : Program}
    (h : ProgramReprWithin m P a n p) : roOn (GF := GF) P m ⊢ astSs a n p :=
  astSs_of_stmtArrayRepr h.1

omit I in

theorem wordAt_of_ownImg {a n v : Nat} {img : Nat → BitVec 8} (h : imgLE img a n = v) :
    ownImg (GF := GF) (InExt (a, n)) img ⊢ wordAt a n v := by
  unfold wordAt
  iintro H
  iexists img
  iframe H %h

omit I in

theorem wordRO_of_ownImg {a n v : Nat} {img : Nat → BitVec 8} (h : imgLE img a n = v) :
    ownImg (GF := GF) (InExt (a, n)) img ⊢ |==> wordRO a n v := by
  iintro H
  imod ownImg_persist _ img $$ H with H
  imodintro
  unfold wordRO
  iexists img
  iframe H %h

omit I in

theorem blockOwn_of_ownImg (a n : Nat) (img : Nat → BitVec 8) :
    ownImg (GF := GF) (InExt (a, n)) img ⊢ blockOwn a n := by
  unfold blockOwn
  iintro H
  iapply ownSet_forget $$ H

def payloadStr : Value → Option String
  | .str s => some s
  | .native f => some (nativeName f)
  | _ => none

def PayloadShared (P : Nat → Prop) (m : Mem) (a : Nat) (v : Value) : Prop :=
  ∀ s, payloadStr v = some s → ∀ p, read64 m (a + 8) = some p → ∀ i, i ≤ s.length → P (p + i)

def closSupply (φc : Addr → Nat) (v : Value) : IProp GF :=
  iprop(∀ ca, ⌜v = .closure ca⌝ → closAt ca (φc ca))

theorem closSupply_of_ne {φc : Addr → Nat} {v : Value} (h : ∀ ca, v ≠ .closure ca) :
    ⊢ closSupply (GF := GF) φc v := by
  unfold closSupply
  iintro %ca %hc
  exact absurd hc (h ca)

theorem valOf_of_valueRepr {P : Nat → Prop} {m : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {a : Nat} {v : Value} (h : ValueRepr m N φc a v) (hsh : PayloadShared P m a v)
    (hwin : SharedWin P) :
    roOn (GF := GF) P m ∗ closSupply φc v ⊢ valImg N (memImg m) a v := by
  cases v with
  | null =>
    simp only [valImg, valOf]
    iintro ⟨-, -⟩
    ipureintro
    rw [imgW_lo32, readLE_memImg h]
  | bool b =>
    obtain ⟨h0, h1⟩ := h
    simp only [valImg, valOf]
    iintro ⟨-, -⟩
    ipureintro
    exact ⟨by rw [imgW_lo32, readLE_memImg h0], by rw [imgW_lo32, readLE_memImg h1]⟩
  | int n =>
    obtain ⟨h0, h1⟩ := h
    unfold readI64 at h1
    obtain ⟨w, hw, hn⟩ := Option.map_eq_some_iff.1 h1
    simp only [valImg, valOf]
    iintro ⟨-, -⟩
    ipureintro
    refine ⟨by rw [imgW_lo32, readLE_memImg h0], ?_⟩
    rw [imgW, readLE_memImg hw]
    exact hn
  | str t =>
    obtain ⟨h0, q, hq, hqne, hstr⟩ := h
    have hw : (imgW (memImg m) (a + 8)).toNat = q := imgW_read64 hq
    simp only [valImg, valOf]
    iintro ⟨#H, -⟩
    isplitr
    · ipureintro
      exact ⟨by rw [imgW_lo32, readLE_memImg h0], by omega⟩
    rw [hw]
    iapply strAt_of_cstringWithin (P := P) (m := m)
      ⟨hstr, fun i hi => hsh t rfl q hq i hi⟩ hwin $$ H
  | closure ca =>
    obtain ⟨h0, hq, hqne⟩ := h
    have hw : (imgW (memImg m) (a + 8)).toNat = φc ca := imgW_read64 hq
    simp only [valImg, valOf, closSupply]
    iintro ⟨-, #H⟩
    isplitr
    · ipureintro
      exact ⟨by rw [imgW_lo32, readLE_memImg h0], by omega⟩
    rw [hw]
    iapply H $$ %ca %rfl
  | native f =>
    obtain ⟨h0, ⟨q, hq, hstr⟩, h2⟩ := h
    have hw : (imgW (memImg m) (a + 8)).toNat = q := imgW_read64 hq
    have hw2 : (imgW (memImg m) (a + 16)).toNat = N.addr f := imgW_read64 h2
    simp only [valImg, valOf]
    iintro ⟨#H, -⟩
    isplitr
    · ipureintro
      exact ⟨by rw [imgW_lo32, readLE_memImg h0], hw2⟩
    rw [hw]
    iapply strAt_of_cstringWithin (P := P) (m := m)
      ⟨hstr, fun i hi => hsh (nativeName f) rfl q hq i hi⟩ hwin $$ H

theorem valImg_congr {N : NativeAddrs} {img : Nat → BitVec 8} {m : Mem} {a : Nat} {v : Value}
    (h : ∀ k, InExt (a, 24) k → img k = memImg m k) :
    valImg (GF := GF) N img a v = valImg N (memImg m) a v := by
  have e0 : imgW img a = imgW (memImg m) a := by
    unfold imgW; rw [imgLE_congr (fun i hi => h (a + i) ⟨by omega, by omega⟩)]
  have e1 : imgW img (a + 8) = imgW (memImg m) (a + 8) := by
    unfold imgW
    rw [imgLE_congr (fun i hi => h (a + 8 + i) ⟨by omega, by omega⟩)]
  have e2 : imgW img (a + 16) = imgW (memImg m) (a + 16) := by
    unfold imgW
    rw [imgLE_congr (fun i hi => h (a + 16 + i) ⟨by omega, by omega⟩)]
  unfold valImg
  rw [e0, e1, e2]

structure FrameReads (m : Mem) (N : NativeAddrs) (φf φc : Addr → Nat) (e : Nat)
    (f : Frame) : Prop where
  count : read32 m e = some f.vars.length
  cap : ∃ cap, read32 m (e + 4) = some cap ∧ f.vars.length ≤ cap
  arrays : ∃ pn pv, read64 m (e + 8) = some pn ∧ read64 m (e + 16) = some pv ∧
    ∀ i, (h : i < f.vars.length) →
      (∃ q, read64 m (pn + 8 * i) = some q ∧ CString m q (f.vars[i].1)) ∧
      ValueRepr m N φc (pv + 24 * i) (f.vars[i].2)
  parentNone : f.parent = none → read64 m (e + 24) = some 0
  parentSome : ∀ pa, f.parent = some pa → read64 m (e + 24) = some (φf pa) ∧ φf pa ≠ 0

theorem FrameReads.of_frameRepr {m : Mem} {N : NativeAddrs} {φf φc : Addr → Nat}
    {e : Nat} {f : Frame} (h : FrameRepr m N φf φc e f) : FrameReads m N φf φc e f where
  count := h.1
  cap := h.2.1
  arrays := h.2.2.1
  parentNone := by
    intro hp
    have := h.2.2.2
    rw [hp] at this
    exact this
  parentSome := by
    intro pa hp
    have := h.2.2.2
    rw [hp] at this
    exact this

omit I in

theorem sepL_of_persistent {α} (H : IProp GF) [Persistent H] (Φ : α → IProp GF) :
    ∀ l : List α, (∀ x ∈ l, H ⊢ Φ x) → H ⊢ sepL l Φ
  | [], _ => by rw [sepL_nil]; iintro -; iempintro
  | x :: xs, h => by
    rw [sepL_cons]
    iintro #Hp
    isplitl []
    · iapply h x (by simp) $$ Hp
    · iapply sepL_of_persistent H Φ xs (fun y hy => h y (by simp [hy])) $$ Hp

omit I in

theorem sepL_zipIdx_of_persistent {α} (H : IProp GF) [Persistent H] (Φ : α × Nat → IProp GF) :
    ∀ (l : List α) (k : Nat), (∀ i, (hi : i < l.length) → H ⊢ Φ (l[i], k + i)) →
      H ⊢ sepL (l.zipIdx k) Φ
  | [], _, _ => by rw [List.zipIdx_nil, sepL_nil]; iintro -; iempintro
  | x :: xs, k, h => by
    rw [List.zipIdx_cons, sepL_cons]
    iintro #Hp
    isplitl []
    · iapply (show H ⊢ Φ (x, k) from h 0 (by simp)) $$ Hp
    · iapply sepL_zipIdx_of_persistent H Φ xs (k + 1) (fun i hi => by
        have := h (i + 1) (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this) $$ Hp

def closSupplyL (φc : Addr → Nat) (vs : List Value) : IProp GF :=
  iprop(□ ∀ v, ⌜v ∈ vs⌝ → closSupply φc v)

instance (φc : Addr → Nat) (vs : List Value) : Persistent (closSupplyL (GF := GF) φc vs) := by
  unfold closSupplyL; infer_instance

def parentSupply (o : Option Addr) (par : Nat) : IProp GF :=
  iprop(∀ pa, ⌜o = some pa⌝ → frameAt pa par)

theorem parentSupply_none (par : Nat) : ⊢ parentSupply (GF := GF) none par := by
  unfold parentSupply
  iintro %pa %h
  exact absurd h (by simp)

structure FrameBridge (P : Nat → Prop) (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (G : FrameGeom) (f : Frame) (img : Nat → BitVec 8) : Prop where
  e_ne : G.e ≠ 0
  sblk : G.sblk.1 ≤ G.e ∧ G.e + 32 ≤ G.sblk.1 + G.sblk.2
  cap : read32 m (G.e + 4) = some G.cap
  names : read64 m (G.e + 8) = some G.pn
  vals : read64 m (G.e + 16) = some G.pv
  parent : read64 m (G.e + 24) = some G.par
  count_le : f.vars.length ≤ G.cap
  empty : G.cap = 0 → G.pn = 0 ∧ G.pv = 0
  arrays : 0 < G.cap → G.nblk = (G.pn, 8 * G.cap) ∧ G.vblk = (G.pv, 24 * G.cap)
  disjoint : G.blocks.Pairwise ExtDisj
  win : ∀ b ∈ G.blocks, BlockWin b
  e_align : G.e % 8 = 0
  cap_canon : G.cap = capFor f.vars.length
  agree : ∀ k, BlocksCover G.blocks k → img k = memImg m k
  nameShared : ∀ i, (h : i < f.vars.length) → ∀ q, read64 m (G.pn + 8 * i) = some q →
    ∀ j, j ≤ (f.vars[i].1).length → P (q + j)
  payloadShared : ∀ i, (h : i < f.vars.length) → PayloadShared P m (G.pv + 24 * i) f.vars[i].2

omit I in

theorem FrameBridge.structCover {P : Nat → Prop} {m : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {G : FrameGeom} {f : Frame} {img : Nat → BitVec 8}
    (h : FrameBridge P m N φc G f img) {i : Nat} (hi : i < 32) :
    BlocksCover G.blocks (G.e + i) := by
  refine ⟨G.sblk, by simp [FrameGeom.blocks], ?_⟩
  unfold InExt
  have := h.sblk
  omega

omit I in

theorem FrameBridge.fieldCover {P : Nat → Prop} {m : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {G : FrameGeom} {f : Frame} {img : Nat → BitVec 8}
    (h : FrameBridge P m N φc G f img) (off : Nat) {i : Nat} (hi : off + i < 32) :
    BlocksCover G.blocks (G.e + off + i) := by
  simpa [show G.e + off + i = G.e + (off + i) by omega] using h.structCover (i := off + i) hi

omit I in

theorem FrameBridge.nameCover {P : Nat → Prop} {m : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {G : FrameGeom} {f : Frame} {img : Nat → BitVec 8}
    (h : FrameBridge P m N φc G f img) {i j : Nat} (hi : i < f.vars.length) (hj : j < 8) :
    BlocksCover G.blocks (G.pn + 8 * i + j) := by
  have hcap : 0 < G.cap := by have := h.count_le; omega
  obtain ⟨h12, -⟩ := h.arrays hcap
  have h1 : G.nblk.1 = G.pn := by rw [h12]
  have h2 : 8 * G.cap ≤ G.nblk.2 := by rw [h12]; exact Nat.le_refl _
  refine ⟨G.nblk, ?_, ?_⟩
  · simp [FrameGeom.blocks, show G.cap ≠ 0 by omega]
  · unfold InExt
    have := h.count_le
    have : 8 * i + 8 ≤ 8 * G.cap := by omega
    omega

omit I in

theorem FrameBridge.valCover {P : Nat → Prop} {m : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {G : FrameGeom} {f : Frame} {img : Nat → BitVec 8}
    (h : FrameBridge P m N φc G f img) {i j : Nat} (hi : i < f.vars.length) (hj : j < 24) :
    BlocksCover G.blocks (G.pv + 24 * i + j) := by
  have hcap : 0 < G.cap := by have := h.count_le; omega
  obtain ⟨-, h34⟩ := h.arrays hcap
  have h3 : G.vblk.1 = G.pv := by rw [h34]
  have h4 : 24 * G.cap ≤ G.vblk.2 := by rw [h34]; exact Nat.le_refl _
  refine ⟨G.vblk, ?_, ?_⟩
  · simp [FrameGeom.blocks, show G.cap ≠ 0 by omega]
  · unfold InExt
    have := h.count_le
    have : 24 * i + 24 ≤ 24 * G.cap := by omega
    omega

omit I in

theorem FrameBridge.word {P : Nat → Prop} {m : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {G : FrameGeom} {f : Frame} {img : Nat → BitVec 8}
    (h : FrameBridge P m N φc G f img) {a n v : Nat} (hread : readLE m a n = some v)
    (hcov : ∀ i, i < n → BlocksCover G.blocks (a + i)) : imgLE img a n = v := by
  rw [imgLE_congr (img' := memImg m) (fun i hi => h.agree _ (hcov i hi)), readLE_memImg hread]

omit I in

theorem frameLayout_of_frameRepr {P : Nat → Prop} {m : Mem} {N : NativeAddrs}
    {φf φc : Addr → Nat} {G : FrameGeom} {f : Frame} {img : Nat → BitVec 8}
    (hrep : FrameReads m N φf φc G.e f) (h : FrameBridge P m N φc G f img) :
    FrameLayout img G f.vars.length where
  e_ne := h.e_ne
  sblk := h.sblk
  count := h.word (a := G.e) (n := 4) hrep.count (fun i hi => h.structCover (by omega))
  cap := h.word h.cap (fun i hi => h.fieldCover 4 (by omega))
  names := h.word h.names (fun i hi => h.fieldCover 8 (by omega))
  vals := h.word h.vals (fun i hi => h.fieldCover 16 (by omega))
  parent := h.word h.parent (fun i hi => h.fieldCover 24 (by omega))
  count_le := h.count_le
  empty := h.empty
  arrays := h.arrays
  disjoint := h.disjoint
  win := h.win
  e_align := h.e_align
  cap_canon := h.cap_canon

theorem bindings_of_frameRepr {P : Nat → Prop} {m : Mem} {N : NativeAddrs}
    {φf φc : Addr → Nat} {G : FrameGeom} {f : Frame} {img : Nat → BitVec 8}
    (hrep : FrameReads m N φf φc G.e f) (h : FrameBridge P m N φc G f img) (hw : SharedWin P) :
    roOn (GF := GF) P m ∗ closSupplyL φc (f.vars.map Prod.snd) ⊢
      bindings N img G.pn G.pv f.vars := by
  obtain ⟨pn, pv, hpn, hpv, hb⟩ := hrep.arrays
  have hpn' : pn = G.pn := Option.some.inj (hpn.symm.trans h.names)
  have hpv' : pv = G.pv := Option.some.inj (hpv.symm.trans h.vals)
  subst hpn'; subst hpv'
  unfold bindings
  iintro #Hall
  iapply sepL_zipIdx_of_persistent _ _ f.vars 0 ?_ $$ Hall
  intro i hi
  simp only [Nat.zero_add]
  obtain ⟨⟨q, hq, hstr⟩, hval⟩ := hb i hi
  have hqw : imgLE img (G.pn + 8 * i) 8 = q :=
    h.word hq (fun j hj => h.nameCover hi hj)
  have hvalimg : valImg (GF := GF) N img (G.pv + 24 * i) f.vars[i].2
      = valImg N (memImg m) (G.pv + 24 * i) f.vars[i].2 :=
    valImg_congr (fun k hk => by
      obtain ⟨hlo, hhi⟩ := hk
      have hcov := h.valCover (j := k - (G.pv + 24 * i)) hi (by omega)
      rw [show G.pv + 24 * i + (k - (G.pv + 24 * i)) = k by omega] at hcov
      exact h.agree k hcov)
  rw [hqw, hvalimg]
  iintro ⟨#H, #Hc⟩
  isplitl []
  · iapply strAt_of_cstringWithin (P := P) (m := m)
      ⟨hstr, fun j hj => h.nameShared i hi q hq j
        (by simpa [String.length] using hj)⟩ hw $$ H
  · iapply valOf_of_valueRepr (P := P) hval (h.payloadShared i hi) hw $$ [H Hc]
    iframe H
    unfold closSupplyL
    iapply Hc $$ %(f.vars[i].2) %(List.mem_map.2 ⟨f.vars[i], List.getElem_mem hi, rfl⟩)

theorem frameBody_of_frameRepr {P : Nat → Prop} {m : Mem} {N : NativeAddrs}
    {φf φc : Addr → Nat} {G : FrameGeom} {f : Frame} {img : Nat → BitVec 8}
    (hrep : FrameReads m N φf φc G.e f) (h : FrameBridge P m N φc G f img) (hw : SharedWin P) :
    roOn (GF := GF) P m ∗ closSupplyL φc (f.vars.map Prod.snd) ∗
      parentSupply f.parent G.par ∗ ownImg (BlocksCover G.blocks) img ⊢ frameBody N f G := by
  unfold frameBody parentSupply
  iintro ⟨#H, #Hc, #Hp, Hown⟩
  iexists img
  isplitr
  · ipureintro; exact frameLayout_of_frameRepr hrep h
  iframe Hown
  isplitl []
  · iapply bindings_of_frameRepr hrep h hw $$ [$]
  · cases hpar : f.parent with
    | none =>
      unfold parentAt
      ipureintro
      exact Option.some.inj ((h.parent).symm.trans (hrep.parentNone hpar))
    | some pa =>
      obtain ⟨hr, hne⟩ := hrep.parentSome pa hpar
      have : G.par = φf pa := Option.some.inj ((h.parent).symm.trans hr)
      unfold parentAt
      isplitr
      · ipureintro; rw [this]; exact hne
      iapply Hp $$ %pa %rfl

end Bridge

end VsaIris.Interp

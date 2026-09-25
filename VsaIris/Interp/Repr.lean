import VsaIris.MallocRun
import VsaIris.Vsa.Stdio
import VsaIris.Vsa.BinDom
import Vsa.RuntimeRepr
import Vsa.MemReprWithin
import Vsa.While.StackNeed
import Vsa.Sim.StoreInvariant

/-!
# Representation predicates (INTERP_DESIGN.md §3, package R)

The interpreter's runtime, owned in the Iris logic.

* Immutable data is PERSISTENT (`↦ₘ□`): C strings (`strAt`), the AST
  (`astE`/`astS`/`astSs`), closure objects (`closOwn`). C never writes or frees
  them after building them.
* Mutable data is EXCLUSIVE and stored as an owned byte image
  (`ownSet S (fun a => a ↦ₘ img a)`) plus pure layout facts about `img`, the
  form `LocalRun`/`wp_seg` consume: a value slot (`valAt`), a frame
  (`frameOwn`), the whole store (`storeRepr`).
* Frame and closure addresses are two ghost maps (`InterpGS`) with persistent
  fragments (`frameAt`, `closAt`): an `Env*` never moves (only its arrays are
  reallocated), and a closure never moves or changes.
* **Live blocks are whole chunk payloads** (user ruling). The store owns every
  byte of the blocks its frames live in (struct, arrays and their spare
  capacity, slack up to the chunk's usable size); `storeRepr s B` lists them
  in `B`, and `world` ties `B` into the allocator's live list `H`.

MachCSL counterparts (xv6iris `8438e55`): read-only data as `↦ₓ□`
(`claude-notes/design/execution-model.md`), one opener for a sealed bundle
(`claude-notes/spec-modules.md`, "Simultaneous borrows of a sealed bundle need
ONE opener"), `kalloc_env (Some n)`/`None` regimes (`iris/KvmSpec.v:123`),
two-owner diagnostics (`claude-notes/durable-notes.md`, "The resource form").
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-! ## Byte images -/

/-- Total little-endian read of `n` bytes of a byte image. -/
def imgLE (img : Nat → BitVec 8) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (img a).toNat + 256 * imgLE img (a + 1) n

/-- The 64-bit word at `a` of an image. -/
def imgW (img : Nat → BitVec 8) (a : Nat) : BitVec 64 := BitVec.ofNat 64 (imgLE img a 8)

/-- An image agrees with a memory on `S`. -/
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

/-- A word of an image agreeing with another on its bytes. -/
theorem imgW_agree {f g : Nat → BitVec 8} {a : Nat} (h : ∀ j, j < 8 → f (a + j) = g (a + j)) :
    imgW f a = imgW g a := by
  unfold imgW; rw [imgLE_congr h]

/-- A memory holding the image on a window reads the image's value. -/
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

/-! ## Owned and read-only bytes -/

section Bytes

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- Exclusive ownership of `S` at the image `img`. -/
abbrev ownImg (S : Nat → Prop) (img : Nat → BitVec 8) : IProp GF :=
  ownSet S (fun a => a ↦ₘ img a)

/-- Read-only bytes. -/
def bytesRO (a : Nat) (bs : List (BitVec 8)) : IProp GF :=
  sepL bs.zipIdx (fun p => (a + p.2) ↦ₘ□ p.1)

instance (a : Nat) (bs : List (BitVec 8)) : Persistent (bytesRO (GF := GF) a bs) := by
  unfold bytesRO; infer_instance

/-- Read-only view of a memory on `P`: every byte of `m` in `P` is owned
read-only at its value. The persistent AST is `ExprReprWithin` over such a
view (`astE`). -/
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

/-- Read one byte out of a view. -/
theorem roOn_byte {P : Nat → Prop} {m : Mem} {k : Nat} {b : BitVec 8} (hk : P k)
    (hb : m[k]? = some b) : roOn (GF := GF) P m ⊢ k ↦ₘ□ b := by
  unfold roOn
  iintro #H
  iapply H $$ %k %b %hk %hb

/-- A read-only byte and an exclusive one are at different addresses. -/
theorem memRO_excl_ne (a a' : Nat) (b b' : BitVec 8) :
    (a ↦ₘ□ b) ∗ (a' ↦ₘ b') ⊢@{IProp GF} ⌜a ≠ a'⌝ := by
  unfold memPointsTo
  iintro ⟨H1, H2⟩
  ihave %h := ghost_map_elem_ne _ _ _ _ _ _ $$ H2 H1
  ipureintro
  exact Ne.symm h

end Bytes

/-! ## Ghost state -/

/-- The interpreter's ghost state (INTERP_DESIGN.md §3): two ghost maps,
spec frame address ↦ machine `Env*` and spec closure address ↦ machine
`Closure*`. Both reuse the machine's `Nat ↦ Nat` ghost-map functor
(`MachPreG.ctlG`), so no second instance of that class is in scope. The
console is `MachGS.conName` (F2). -/
class InterpGS (GF : BundledGFunctors) where
  frameName : GName
  closName : GName

section Repr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- Spec frame `fa` lives at machine `Env*` `e`, forever. -/
def frameAt (fa e : Nat) : IProp GF := ghost_map_elem I.frameName DFrac.discard fa e
/-- Spec closure `ca` lives at machine `Closure*` `p`, forever. -/
def closAt (ca p : Nat) : IProp GF := ghost_map_elem I.closName DFrac.discard ca p

instance (fa e : Nat) : Persistent (frameAt (GF := GF) fa e) := by unfold frameAt; infer_instance
instance (ca p : Nat) : Persistent (closAt (GF := GF) ca p) := by unfold closAt; infer_instance

theorem frameAt_agree (fa e e' : Nat) : frameAt (GF := GF) fa e ∗ frameAt fa e' ⊢ ⌜e = e'⌝ := by
  unfold frameAt; exact ghost_map_elem_agree _ _ _ _ _ _
theorem closAt_agree (ca p p' : Nat) : closAt (GF := GF) ca p ∗ closAt ca p' ⊢ ⌜p = p'⌝ := by
  unfold closAt; exact ghost_map_elem_agree _ _ _ _ _ _

/-! ## Read-only images, strings, the AST -/

/- `roImg` (`S` owned read-only at an image) is in `VsaIris/Vsa/ImpureRO.lean`. -/

/-- The binary's `.text` and `.rodata`, persistent (newlib's code and every
constant a helper reads; `world` owns it). -/
def _root_.VsaIris.Newlib.binImg : IProp GF :=
  iprop(roImg Newlib.textDom Newlib.textByte ∗ roImg Newlib.rodataDom Newlib.rodataByte)

instance : Persistent (Newlib.binImg (GF := GF)) := by unfold Newlib.binImg; infer_instance

/-- The bytes of a C string: ASCII, nonzero, then a NUL (`CStr`). -/
def CStrImg (img : Nat → BitVec 8) (p : Nat) (s : String) : Prop :=
  (∀ i (h : i < s.toList.length), img (p + i) = BitVec.ofNat 8 (s.toList[i]).toNat ∧
      0 < (s.toList[i]).toNat ∧ (s.toList[i]).toNat < 128) ∧
    img (p + s.toList.length) = 0

/-- The HTIF `tohost`/`fromhost` words start here (`Vsa.Sim.tohostAddr`;
`VsaIris/Interp/SpecEnv.lean` checks the two agree). -/
def htifLo : Nat := 0x8001ad00

/-- **The window a word-at-a-time string routine reads.** `strlen` and
`strcmp` load whole aligned 8-byte words, so they read up to 7 bytes past
the NUL of a `len`-character string at `p`: the window `[p, p + len + 8)`
must be RAM and off the HTIF words. -/
structure StrWin (p len : Nat) : Prop where
  lo : 0x80000000 ≤ p
  hi : p + len + 8 ≤ 0x100000000
  htif : p + len + 8 ≤ htifLo ∨ htifLo + 16 ≤ p

/-- A C string at `p`, NUL included, read-only forever (`CString`), with the
window `strlen`/`strcmp` over-read (`StrWin`). -/
def strAt (p : Nat) (s : String) : IProp GF :=
  iprop(∃ img, ⌜CStrImg img p s ∧ StrWin p s.toList.length⌝ ∗
    roImg (InExt (p, s.toList.length + 1)) img)

instance (p : Nat) (s : String) : Persistent (strAt (GF := GF) p s) := by
  unfold strAt; infer_instance

/-- Persistent AST ownership: `ExprReprWithin` over a read-only view. The
view `m` and its allowed bytes `P` are existential; every consumer reads
through the representation derivation (child projections, reads), and two
views agree where both are defined (`roOn` fragments are one ghost map). -/
def astE (a : Nat) (e : Expr) : IProp GF :=
  iprop(∃ (P : Nat → Prop) (m : Mem), ⌜ExprReprWithin m P a e⌝ ∗ roOn P m)
def astS (a : Nat) (s : Stmt) : IProp GF :=
  iprop(∃ (P : Nat → Prop) (m : Mem), ⌜StmtReprWithin m P a s⌝ ∗ roOn P m)
def astSs (a n : Nat) (ss : List Stmt) : IProp GF :=
  iprop(∃ (P : Nat → Prop) (m : Mem), ⌜StmtArrayReprWithin m P a n ss⌝ ∗ roOn P m)

instance (a : Nat) (e : Expr) : Persistent (astE (GF := GF) a e) := by unfold astE; infer_instance
instance (a : Nat) (s : Stmt) : Persistent (astS (GF := GF) a s) := by unfold astS; infer_instance
instance (a n : Nat) (ss : List Stmt) : Persistent (astSs (GF := GF) a n ss) := by
  unfold astSs; infer_instance

/-! ## Values -/

/-- The meaning of a 24-byte `Value`'s three words (`ValueRepr`), persistent. -/
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

/-- The value stored at `a` of an image. -/
abbrev valImg (N : NativeAddrs) (img : Nat → BitVec 8) (a : Nat) (v : Value) : IProp GF :=
  valOf N v (imgW img a) (imgW img (a + 8)) (imgW img (a + 16))

/-- A 24-byte slot of unknown contents (an sret buffer, a spare slot). -/
def slot24 (a : Nat) : IProp GF := blockOwn a 24

/-- A represented value in an owned 24-byte slot (`ValueWordRepr`). -/
def valAt (N : NativeAddrs) (a : Nat) (v : Value) : IProp GF :=
  iprop(∃ img, ownImg (InExt (a, 24)) img ∗ valImg N img a v)

theorem valAt_slot (N : NativeAddrs) (a : Nat) (v : Value) :
    valAt (GF := GF) N a v ⊢ slot24 a := by
  unfold valAt slot24 blockOwn
  iintro ⟨%img, H, -⟩
  iapply ownSet_forget $$ H

/-! ## Closures -/

/-- A closure object (`ClosureRepr`), persistent: its 16 bytes (`fn_expr`,
`env`), the `EX_FN` node, and the captured frame's address. -/
def closOwn (ca : Nat) (cd : ClosureData) : IProp GF :=
  iprop(∃ (p q e : Nat) (img : Nat → BitVec 8), closAt ca p ∗
    ⌜p ≠ 0 ∧ e ≠ 0 ∧ imgLE img p 8 = q ∧ imgLE img (p + 8) 8 = e⌝ ∗
    roImg (InExt (p, 16)) img ∗ astE q (.fn cd.name cd.params cd.body) ∗ frameAt cd.env e)

instance (ca : Nat) (cd : ClosureData) : Persistent (closOwn (GF := GF) ca cd) := by
  unfold closOwn; infer_instance

/-! ## Frames -/

/-- Where one frame lives: the `Env` struct at `e` inside the block `sblk`,
the two arrays at the starts of `nblk`/`vblk` (absent while `cap = 0`), and
the struct's words. -/
structure FrameGeom where
  e : Nat
  cap : Nat
  pn : Nat
  pv : Nat
  par : Nat
  sblk : Nat × Nat
  nblk : Nat × Nat
  vblk : Nat × Nat

/-- The heap blocks a frame owns: whole chunk payloads. -/
def FrameGeom.blocks (G : FrameGeom) : List (Nat × Nat) :=
  G.sblk :: (if G.cap = 0 then [] else [G.nblk, G.vblk])

/-- Byte `a` lies in one of the blocks. -/
def BlocksCover (bl : List (Nat × Nat)) (a : Nat) : Prop := ∃ b ∈ bl, InExt b a

/-- Two extents share no byte. -/
def ExtDisj (b b' : Nat × Nat) : Prop := ∀ a, InExt b a → ¬ InExt b' a

/-- Where a heap block may sit: RAM above the HTIF words, 16-aligned (a chunk
payload). The `env_*` loads and stores into a frame need exactly this. -/
structure BlockWin (b : Nat × Nat) : Prop where
  lo : 0x80000000 ≤ b.1
  hi : b.1 + b.2 ≤ 0x100000000
  htif : htifLo + 16 ≤ b.1
  align : b.1 % 16 = 0

/-- The capacity `env_define`'s growth policy reaches for `k` bindings
(`env.c:29-33`: `cap = cap ? 2*cap : 8`), by the same fuel recursion as the
cost model's `arrayCostAux` (`Vsa/While/Cost.lean`), so the two are related
step by step. -/
def capForAux : (fuel cap k : Nat) → Nat
  | 0, cap, _ => cap
  | fuel + 1, cap, k => if k ≤ cap then cap else capForAux fuel (if cap = 0 then 8 else 2 * cap) k

/-- The canonical capacity of a frame with `k` bindings: `0, 8, 16, 32, …`. -/
def capFor (k : Nat) : Nat := capForAux k 0 k

/-- The pure layout of one frame in its image (`FrameRepr`'s struct words,
plus the block geometry `env_define`'s `realloc` needs, the blocks' address
windows the `env_*` loads and stores need, and the canonical capacity the
counted regime's charges follow). -/
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

/-- The arrays' extents, componentwise. -/
theorem FrameLayout.arrays_le {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) (hc : 0 < G.cap) :
    G.nblk.1 = G.pn ∧ 8 * G.cap ≤ G.nblk.2 ∧ G.vblk.1 = G.pv ∧ 24 * G.cap ≤ G.vblk.2 := by
  obtain ⟨h1, h2⟩ := h.arrays hc
  rw [h1, h2]; exact ⟨rfl, Nat.le_refl _, rfl, Nat.le_refl _⟩

/-- The bindings of a frame: name `i` is the string at `names[i]`, value `i`
the words at `vals[i]` (persistent meanings; the words are in the image). -/
def bindings (N : NativeAddrs) (img : Nat → BitVec 8) (pn pv : Nat)
    (vars : List (String × Value)) : IProp GF :=
  sepL vars.zipIdx (fun p =>
    iprop(strAt (imgLE img (pn + 8 * p.2) 8) p.1.1 ∗ valImg N img (pv + 24 * p.2) p.1.2))

instance (N : NativeAddrs) (img : Nat → BitVec 8) (pn pv : Nat) (vars : List (String × Value)) :
    Persistent (bindings (GF := GF) N img pn pv vars) := by
  unfold bindings; infer_instance

/-- The parent link (`NULL` iff no parent). -/
def parentAt : Option Addr → Nat → IProp GF
  | none, par => iprop(⌜par = 0⌝)
  | some pa, par => iprop(⌜par ≠ 0⌝ ∗ frameAt pa par)

instance (o : Option Addr) (par : Nat) : Persistent (parentAt (GF := GF) o par) := by
  cases o <;> unfold parentAt <;> infer_instance

/-- One frame's contents at geometry `G`, without its address fragment:
the whole image of its blocks, exclusively, and the persistent meanings. -/
def frameBody (N : NativeAddrs) (f : Frame) (G : FrameGeom) : IProp GF :=
  iprop(∃ img, ⌜FrameLayout img G f.vars.length⌝ ∗ ownImg (BlocksCover G.blocks) img ∗
    bindings N img G.pn G.pv f.vars ∗ parentAt f.parent G.par)

/-- One frame (`FrameRepr` + ownership of its struct and array blocks). -/
def frameOwn (N : NativeAddrs) (fa : Addr) (f : Frame) (bl : List (Nat × Nat)) : IProp GF :=
  iprop(∃ G : FrameGeom, ⌜bl = G.blocks⌝ ∗ frameAt fa G.e ∗ frameBody N f G)

/-- The frames `i, i+1, …` with their block lists. -/
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

/-- The closures `i, i+1, …`, persistent. -/
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

/-- The two address maps cover exactly the allocated prefixes; closure
addresses are injective (`Value.equal` on closures compares pointers).
Frame-address injectivity is not stated: it follows from ownership
(`storeRepr_frame_inj`). -/
structure StoreMaps (mf mc : NatMap Nat) (s : Store) : Prop where
  frames : ∀ k, (PartialMap.get? mf k).isSome ↔ k < s.frames.size
  closures : ∀ k, (PartialMap.get? mc k).isSome ↔ k < s.closures.size
  clos_inj : ∀ a b p, PartialMap.get? mc a = some p → PartialMap.get? mc b = some p → a = b

/-- The pure part of `storeRepr`: the two address maps, the block list, the
closure-body bound and the environment invariant (`Vsa.Sim.StoreInvariant`:
unique names per frame, parents point to older frames). `env_get`/`env_set`
walk the parent chain by it, and `env_define` updates the first match by it. -/
structure StorePure (mf mc : NatMap Nat) (s : Store) (B : List (Nat × Nat))
    (Bs : List (List (Nat × Nat))) : Prop where
  maps : StoreMaps mf mc s
  blocks : B = Bs.flatten
  bodies : StoreBodiesBound s perCallBudget
  inv : Vsa.Sim.StoreInvariant s

/-- **The whole store** (`StoreRepr` + `HeapOwned` + `StoreOwned`),
monolithic: BigStep's frames are shared by closures, so every call can reach
any frame. `B` is the list of heap blocks the frames own. -/
def storeRepr (N : NativeAddrs) (s : Store) (B : List (Nat × Nat)) : IProp GF :=
  iprop(∃ (mf mc : NatMap Nat) (Bs : List (List (Nat × Nat))),
    ghost_map_auth I.frameName (DFrac.own 1) mf ∗ ghost_map_auth I.closName (DFrac.own 1) mc ∗
    ⌜StorePure mf mc s B Bs⌝ ∗
    framesOwn N 0 s.frames.toList Bs ∗ closuresOwn 0 s.closures.toList)

/-! ## The interpreter context -/

/-- `struct Interp` (`c/src/interp.h`): `globals` @0, `call_depth` @8,
`on_error` @16 (newlib's riscv `jmp_buf`, 26 words; `setjmp` fills the first
14, `Vsa/Sim/JmpSpec.lean`), `err_msg[256]` @224 (`runtime_error`:
`addi a0,s0,224`; `main`: `addi a2,sp,496` with `in = sp+272`). -/
def interpDepthOff : Nat := 8
def interpJmpOff : Nat := 16
def interpJmpLen : Nat := 208
def interpErrOff : Nat := 224
def interpErrLen : Nat := 256

/-- An exclusively owned `n`-byte little-endian word holding `v`. -/
def wordAt (a n v : Nat) : IProp GF :=
  iprop(∃ img, ownImg (InExt (a, n)) img ∗ ⌜imgLE img a n = v⌝)

/-- A read-only `n`-byte little-endian word holding `v`. -/
def wordRO (a n v : Nat) : IProp GF :=
  iprop(∃ img, roImg (InExt (a, n)) img ∗ ⌜imgLE img a n = v⌝)

instance (a n v : Nat) : Persistent (wordRO (GF := GF) a n v) := by
  unfold wordRO; infer_instance

/-- `err_msg` at any contents. -/
def errAny (inp : Nat) : IProp GF := blockOwn (inp + interpErrOff) interpErrLen

/-- `err_msg` holding a C string: a NUL within its 256 bytes. `runtime_error`'s
`snprintf` leaves it so, and `main`'s `fprintf("%s\n", in->err_msg)` reads it
(H5). -/
def errStr (inp : Nat) : IProp GF :=
  iprop(∃ img, ownImg (InExt (inp + interpErrOff, interpErrLen)) img ∗
    ⌜∃ k, k < interpErrLen ∧ img (inp + interpErrOff + k) = 0⌝)

/-- The fields every mode shares, with `err_msg` as `E`: `globals` read-only
(it points at frame 0 forever), `call_depth = d` exclusive (with its
padding), and `d ≤ maxCallDepth` (`call_value` checks `++call_depth >
MAX_CALL_DEPTH` before a body runs and resets it on the error; lane E4: the
closure call's signed depth test agrees with `Call.closure`'s `d <
maxCallDepth` only below `2^31`). -/
def interpCoreE (inp d : Nat) (E : IProp GF) : IProp GF :=
  iprop(∃ g, wordRO inp 8 g ∗ frameAt 0 g ∗ wordAt (inp + interpDepthOff) 4 d ∗
    ⌜d ≤ Vsa.While.maxCallDepth⌝ ∗ blockOwn (inp + interpDepthOff + 4) 4 ∗ E)

/-- The fields every mode shares; `err_msg` exclusive at any contents. -/
def interpCore (inp d : Nat) : IProp GF := interpCoreE inp d (errAny inp)

/-- The `jmp_buf` read-only at the image `jb`. -/
def jmpRO (inp : Nat) (jb : Nat → BitVec 8) : IProp GF :=
  roImg (InExt (inp + interpJmpOff, interpJmpLen)) jb

instance (inp : Nat) (jb : Nat → BitVec 8) : Persistent (jmpRO (GF := GF) inp jb) := by
  unfold jmpRO; infer_instance

/-- The context inside `interp_run`, after `setjmp`, with `err_msg` as `E`:
the `jmp_buf` is read-only (H5 reads the landing registers off it), its saved
`ra` word 4-aligned (`runtime_error`'s `longjmp` returns there; `setjmp`
stored `0x80004428`; lane E4: every `runtime_error` site needs it, in either
mode). -/
def interpCtxE (inp d : Nat) (E : IProp GF) : IProp GF :=
  iprop(interpCoreE inp d E ∗ ∃ jb, jmpRO inp jb ∗ ⌜(imgW jb (inp + interpJmpOff)).toNat % 4 = 0⌝)

/-- The context inside `interp_run`, after `setjmp`. -/
def interpCtx (inp d : Nat) : IProp GF := interpCtxE inp d (errAny inp)

/-- The context at `interp_run`'s entry (A0), before `setjmp`: the `jmp_buf`
is exclusive. -/
def interpCtxPre (inp d : Nat) : IProp GF :=
  iprop(interpCore inp d ∗ blockOwn (inp + interpJmpOff) interpJmpLen)

/-! ## The heap and the world -/

/-- MachCSL's two allocator regimes (`KvmSpec.v:123` `kalloc_env γ (Some n)` /
`None`, paper §6.5): counted (total mode; cannot fail) and uncounted (partial
mode; malloc may return NULL). -/
inductive Regime where
  | counted (k : Nat)
  | uncounted

def heapRes (L : DlLayout) (Room : RoomPred) : Regime → List (Nat × Nat) → IProp GF
  | .counted k, H => isHeapRoom L Room H k
  | .uncounted, H => isHeap L H

omit I in
theorem heapRes_isHeap (L : DlLayout) (Room : RoomPred) (ρ : Regime) (H : List (Nat × Nat)) :
    heapRes (GF := GF) L Room ρ H ⊢ isHeap L H := by
  cases ρ with
  | counted k => exact isHeapRoom_forget L Room H k
  | uncounted => exact .rfl

/-- Everything an evaluation threads, with `err_msg` as `E`: heap, store,
console, newlib's runtime data, interpreter context. `B ⊆ H`: the store's
blocks are live, so `free`/`realloc` of a frame array finds its block in
`H`. -/
def worldE (E : IProp GF) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (ρ : Regime) (st : St) (d : Nat) : IProp GF :=
  iprop(∃ H B, heapRes L Room ρ H ∗ storeRepr N st.store B ∗ consoleOwn st.out ∗
    Stdio.stdioOwn ∗ interpCtxE inp d E ∗ ⌜∀ b ∈ B, b ∈ H⌝ ∗ Newlib.binImg)

/-- Everything an evaluation threads. -/
def world (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (ρ : Regime) (st : St) (d : Nat) : IProp GF :=
  worldE (errAny inp) N L Room inp ρ st d

/-- The binary's image, out of the world (persistent). -/
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

end Repr

end VsaIris.Interp

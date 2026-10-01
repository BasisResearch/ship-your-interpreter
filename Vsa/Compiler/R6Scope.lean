import Vsa.Compiler.SUpd

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- The frame of scope `a` (store frame `fr`) at address `f` with names `L`: its contents and the
read obligations of its words. -/
structure HeadFrame (F : FrMap) (H : CloMap) (m : Mem) (h : Nat) (fr : Frame) (f : Nat) (L : List String) :
    Prop where
  fat : FrameAt H m h f L (parAddr F fr) fr
  lo : frameBase ≤ f
  hi : f + 8 + 16 * L.length ≤ frameEnd
  len : L.length ≤ 120
  al : f % 8 = 0
  nat : (BitVec.ofNat 64 f).toNat = f
  ld : LdOK f

theorem StoreRel.headFrame {F : FrMap} {H : CloMap} {s : Store} {m : Mem} {hF h : Nat}
    (hs : StoreRel F H s m hF h) {a : Addr} {fr : Frame} {f0 f : Nat} {L L' : List String}
    (hfr : s.frames[a]? = some fr) (hF0 : F[a]? = some (f0, L)) (hFa : F[a]? = some (f, L')) :
    HeadFrame F H m h fr f L := by
  have hb : frameBase = 0x80100000 := rfl
  have he : frameEnd = 0x90000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  rw [hF0] at hFa; cases hFa
  obtain ⟨h1, h2, h3, h4⟩ := hs.region a f0 L hF0
  have := hs.top
  unfold frSize at h2
  exact ⟨hs.frame a fr f0 L hfr hF0, h1, by omega, h4, h3, toNat_ofNat_lt (by omega), by unfold LdOK; omega⟩

/-- Scope pop, machine side: the frame's first word is the parent frame's address. -/
theorem HeadFrame.word {F : FrMap} {H : CloMap} {m : Mem} {h : Nat} {fr : Frame} {f : Nat} {L : List String}
    (hd : HeadFrame F H m h fr f L) {b : Addr} (hpar : fr.parent = some b) :
    rdW m f = BitVec.ofNat 64 (parOf F (some b)) := by
  rw [hd.fat.parent, parAddr_eq_parOf, hpar]

theorem parOf_of {F : FrMap} {b : Addr} {fb : Nat} {L : List String} (hFb : F[b]? = some (fb, L)) :
    parOf F (some b) = fb := by simp [parOf, hFb]

/-- Scope pop, source side. -/
theorem ChainL.pop {F : FrMap} {s : Store} {inner env : Addr} {L : List String} {Γ : List (List String)}
    (hc : ChainL F s inner (L :: Γ)) {fr : Frame} (hfr : s.frames[inner]? = some fr)
    (hpar : fr.parent = some env) : ChainL F s env Γ := by
  cases hc with
  | top _ hp' _ => rw [hfr] at *; simp_all
  | cons hfr' hpar' _ hc =>
    rw [hfr] at hfr'; cases hfr'; rw [hpar] at hpar'; cases hpar'; exact hc

end Vsa.Compiler

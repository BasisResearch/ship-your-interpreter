import Vsa.AbsInt.Domains.Product
import Vsa.AbsInt.Domains.Kinds
import Vsa.AbsInt.Domains.Sign

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

class ToItv (A : Type) where
  toItv : A → Itv

class ToItvLaw (A : Type) [AbsDom A] [ToItv A] : Prop where
  sound : ∀ {a : A} {v : Value}, Gam a v → Itv.Gam (ToItv.toItv a) v

namespace Itv

def meet : Itv → Itv → Itv
  | bot, _ => bot
  | _, bot => bot
  | top, b => b
  | a, top => a
  | range l1 h1, range l2 h2 => mk (maxLo l1 l2) (minHi h1 h2)

theorem gam_meet {a b : Itv} {v : Value} (ha : Gam a v) (hb : Gam b v) : Gam (meet a b) v := by
  cases a with
  | bot => exact ha.elim
  | top => cases b <;> first | exact hb.elim | exact hb
  | range l1 h1 =>
    cases b with
    | bot => exact hb.elim
    | top => exact ha
    | range l2 h2 =>
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [Gam] at ha
      exact gam_mk (inLo_maxLo ha.1 hb.1) (inHi_minHi ha.2 hb.2)

end Itv

instance : ToItv Itv := ⟨id⟩
instance : ToItvLaw Itv := ⟨fun h => h⟩

instance : ToItv Const where
  toItv
    | .val (.int n) => .range (some n) (some n)
    | .bot => .bot
    | _ => .top

instance : ToItvLaw Const where
  sound {a v} h := by
    cases a with
    | bot => exact h.elim
    | top => trivial
    | val w =>
      simp only [AbsDom.Gam, Const.Gam] at h
      subst h
      cases v with
      | int n => exact Itv.gam_single
      | _ => trivial

instance : ToItv KSet where
  toItv a := if a = { int := true } then .range none none else if a = {} then .bot else .top

instance : ToItvLaw KSet where
  sound {a v} h := by
    show Itv.Gam (if a = { int := true } then .range none none else if a = {} then .bot else .top) v
    split
    · rename_i ha
      subst ha
      rcases v with _ | _ | n | _ | _ | (_ | _ | _) <;> simp_all [AbsDom.Gam, KSet.Mem] <;>
        exact ⟨trivial, trivial⟩
    · split
      · rename_i _ ha
        subst ha
        rcases v with _ | _ | n | _ | _ | (_ | _ | _) <;> simp_all [AbsDom.Gam, KSet.Mem]
      · trivial

instance : ToItv Sign where
  toItv a :=
    if a.other then .top
    else Itv.mk (if a.neg then none else if a.zero then some 0 else some 1)
      (if a.pos then none else if a.zero then some 0 else some (-1))

instance : ToItvLaw Sign where
  sound {a v} h := by
    show Itv.Gam (if a.other then .top
      else Itv.mk (if a.neg then none else if a.zero then some 0 else some 1)
        (if a.pos then none else if a.zero then some 0 else some (-1))) v
    split
    · trivial
    · rename_i ho
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [AbsDom.Gam, Sign.Gam] at h <;>
        try exact absurd h ho
      apply Itv.gam_mk
      · by_cases h1 : n < 0
        · simp only [Sign.hasInt, h1, ↓reduceIte] at h
          simp [h, Itv.InLo]
        · by_cases h2 : n = 0
          · subst h2
            simp only [Sign.hasInt, Int.lt_irrefl, ↓reduceIte] at h
            split
            · trivial
            · simp [h, Itv.InLo]
          · split
            · trivial
            · split <;> simp only [Itv.InLo] <;> omega
      · by_cases h1 : 0 < n
        · have h1' : ¬ n < 0 := by omega
          have h2 : ¬ n = 0 := by omega
          simp only [Sign.hasInt, h1', h2, ↓reduceIte] at h
          simp [h, Itv.InHi]
        · by_cases h2 : n = 0
          · subst h2
            simp only [Sign.hasInt, Int.lt_irrefl, ↓reduceIte] at h
            split
            · trivial
            · simp [h, Itv.InHi]
          · split
            · trivial
            · split <;> simp only [Itv.InHi] <;> omega

instance {A B : Type} [ToItv A] [ToItv B] : ToItv (A × B) :=
  ⟨fun p => Itv.meet (ToItv.toItv p.1) (ToItv.toItv p.2)⟩

instance {A B : Type} [AbsDom A] [AbsDom B] [Reduce A B] [ToItv A] [ToItv B]
    [ToItvLaw A] [ToItvLaw B] : ToItvLaw (A × B) :=
  ⟨fun h => Itv.gam_meet (ToItvLaw.sound h.1) (ToItvLaw.sound h.2)⟩

end Vsa.AbsInt

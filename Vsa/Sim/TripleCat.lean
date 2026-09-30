import Vsa.Triple

open Vsa.Machine (Config)

namespace Vsa.Logic

def Ent (P Q : Config → Prop) : Prop := ∀ c, P c → Q c

namespace Ent

@[refl] theorem refl (P : Config → Prop) : Ent P P := fun _ h => h

theorem trans {P Q R : Config → Prop} (h₁ : Ent P Q) (h₂ : Ent Q R) : Ent P R :=
  fun c hc => h₂ c (h₁ c hc)

end Ent

scoped infixr:25 " ⊢ₑ " => Ent

namespace Triple

theorem dimap {P P' Q Q' : Config → Prop}
    (pre : Ent P' P) (post : Ent Q Q') (t : Triple P Q) : Triple P' Q' :=
  Triple.conseq t pre post

@[simp] theorem dimap_id {P Q : Config → Prop} (t : Triple P Q) :
    dimap (Ent.refl P) (Ent.refl Q) t = t := Subsingleton.elim _ _

@[simp] theorem dimap_dimap {P P' P'' Q Q' Q'' : Config → Prop}
    (f' : Ent P' P) (g' : Ent Q Q') (f : Ent P'' P') (g : Ent Q' Q'')
    (t : Triple P Q) :
    dimap f g (dimap f' g' t) = dimap (Ent.trans f f') (Ent.trans g' g) t :=
  Subsingleton.elim _ _

@[simp] theorem seq_assoc {P Q R S : Config → Prop}
    (a : Triple P Q) (b : Triple Q R) (c : Triple R S) :
    (a.seq b).seq c = a.seq (b.seq c) := Subsingleton.elim _ _

end Triple

structure PredIso (P Q : Config → Prop) : Prop where
  to  : Ent P Q
  inv : Ent Q P

namespace PredIso

theorem trans {P Q R : Config → Prop} (h₁ : PredIso P Q) (h₂ : PredIso Q R) :
    PredIso P R := ⟨Ent.trans h₁.to h₂.to, Ent.trans h₂.inv h₁.inv⟩

end PredIso

universe u v w

end Vsa.Logic

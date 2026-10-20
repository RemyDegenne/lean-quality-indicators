@[expose] public section

universe w v u

namespace CategoryTheory.Functor

open Opposite

variable {C : Type u} [Category.{v} C]

variable {F : Cᵒᵖ ⥤ Type w} {X : C} {x : F.obj (op X)}

lemma IsRepresentedBy.iff_exists_representableBy :
    F.IsRepresentedBy x ↔ ∃ (R : F.RepresentableBy X), R.homEquiv (𝟙 X) = x :=
  ⟨fun h ↦ ⟨h.representableBy, by simp⟩, fun ⟨R, h⟩ ↦ h ▸ R.isRepresentedBy⟩

end CategoryTheory.Functor
end

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

section Pushout

@[simp]
lemma hasPullback_unop_iff_hasPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPullback f.unop g.unop ↔ HasPushout f g := by
  rw [HasPullback, hasLimit_iff_of_iso (cospanUnop f g), hasLimit_inverse_equivalence_comp_iff,
    hasLimit_leftOp_iff_hasColimit]

end Pushout
end CategoryTheory.Limits
end
end

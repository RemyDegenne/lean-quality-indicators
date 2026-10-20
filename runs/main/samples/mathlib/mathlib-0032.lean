public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C]

variable {P Q W : MorphismProperty C}

section CodescendsAlong

variable {Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A}

lemma CodescendsAlong.mk' [P.RespectsIso]
    (H : ∀ {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} [HasPushout f g], Q f → P (pushout.inl f g) → P g) :
    P.CodescendsAlong Q where
  of_isPushout {A X Y Z f g inl inr} h hf hfst := by
    have : HasPushout f g := h.hasPushout
    apply H hf
    rwa [← P.cancel_right_of_respectsIso _ h.isoPushout.inv, h.inl_isoPushout_inv]

end CodescendsAlong
end CategoryTheory.MorphismProperty
end

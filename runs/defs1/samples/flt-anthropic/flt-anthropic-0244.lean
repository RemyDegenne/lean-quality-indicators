set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace NeronSpecialFibreInfra

section FibreRestrictAlong

variable {B C X Y Z : Scheme.{u}}

def fibreRestrictAlong (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B) (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g c) (pullback.snd f c) :=
  ⟨pullback.lift (pullback.fst g c ≫ φ.1) (pullback.snd g c)
      (by rw [Category.assoc, φ.2, pullback.condition]),
    pullback.lift_snd _ _ _⟩

end FibreRestrictAlong
end NeronSpecialFibreInfra
end

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ u₁ v₂ u₂ v u

section SmallModel

variable (A : Type u)

attribute [local instance] smallDelignePreadditive

attribute [local instance] smallDeligneInverseAdditive

attribute [local instance] smallDeligneFunctorAdditive

attribute [local instance] smallDeligneLinear

attribute [local instance] smallDeligneInverseLinear

attribute [local instance] smallDeligneFunctorLinear

attribute [local instance] smallDeligneFiniteLimits

attribute [local instance] smallDeligneAbelian

attribute [local instance] smallDeligneBiproducts

attribute [local instance] smallDeligneMonoidalPreadditive

attribute [local instance] smallDeligneMonoidalLinear

attribute [local instance] smallDeligneRigid

theorem deligneTheoremStatement_of_small
    (h : ∀ (B : Type v) [SmallCategory B] [Abelian B] [Linear ℂ B]
        [MonoidalCategory B] [SymmetricCategory B] [MonoidalPreadditive B]
        [MonoidalLinear ℂ B] [HasFiniteBiproducts B] [RigidCategory B],
      HasScalarUnit B → (∃ X : B, TensorGeneratedBy B X) →
        ModerateLengthGrowth B → Nonempty (DeligneFibreFunctor B)) :
    DeligneTheoremStatement.{u, v} := by
  intro A _ _ _ _ _ _ _ _ _ _ hunit hgen hgrow
  obtain ⟨X, hX⟩ := hgen
  obtain ⟨F⟩ := h (SmallDeligne A)
    (hasScalarUnit_of_fullyFaithful (smallDeligneEquiv A).inverse
      (smallDeligneEquiv A).fullyFaithfulInverse hunit)
    ⟨(smallDeligneEquiv A).functor.obj X,
      tensorGeneratedBy_map (smallDeligneEquiv A) hX⟩
    (moderateLengthGrowth_map (smallDeligneEquiv A) hgrow)
  exact ⟨F.precompose (smallDeligneEquiv A).functor⟩

end SmallModel
end RS
end

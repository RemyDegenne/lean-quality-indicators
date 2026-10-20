@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace KTheory

variable (R : Type u) [Ring R]

attribute [local instance] directSumCartesian

attribute [local instance] directSumBraided

attribute [local instance] directSumSymmetric

attribute [local instance] smallAdditiveSkeleton

namespace ProjectiveClass

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

section Lift

variable {A : Type w} [AddZero A]
  (f : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ → A)
  (hiso : ∀ {X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ}, (X ≅ Y) → f X = f Y)
  (hzero : f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1}) = 0)
  (hadd : ∀ X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ,
    f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) = f X + f Y)

/-- Descend an isomorphism-invariant function on finite projective right modules
which preserves zero and direct sum to an additive map on their class monoid. -/
@[no_expose]
noncomputable def lift : ProjectiveClass R →+ A where
  toFun := liftFunction R f hiso
  map_zero' := by
    simpa only [of_zero] using
      (liftFunction_of R f hiso
        (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1})).trans hzero
  map_add' a b := by
    obtain ⟨X, rfl⟩ := of_surjective R a
    obtain ⟨Y, rfl⟩ := of_surjective R b
    rw [← of_prod R X Y]
    calc
      liftFunction R f hiso (of R (X × Y)) =
          f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) :=
        liftFunction_of R f hiso (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y))
      _ = f X + f Y := hadd X Y
      _ = liftFunction R f hiso (of R X) + liftFunction R f hiso (of R Y) := by
        rw [liftFunction_of, liftFunction_of]

end Lift
end ProjectiveClass
end KTheory
end

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

section Lift

variable {C : Type uC} [Ring C] [Algebra R C]
  (𝒞 : ℤ → Submodule R C) [GradedAlgebra 𝒞]

/-- The graded algebra map out of a graded tensor product induced by two graded algebra maps whose
images satisfy the Koszul commutation rule. -/
noncomputable def gradedTensorLift (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)) :
    gradedTensorGrading 𝒜 ℬ →ₐᵍ[R] 𝒞 := by
  have h' : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j),
      f.toAlgHom a * g.toAlgHom b = (-1 : ℤˣ) ^ (j * i) •
        (g.toAlgHom b * f.toAlgHom a) := by
    intro i j a b
    -- Mathlib's lift accepts the stored `AlgHom`s, whose applications are definitionally the
    -- applications of the graded maps in the supplied commutation hypothesis.
    change f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)
    exact h a b
  let F : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C :=
    GradedTensorProduct.lift 𝒜 ℬ f.toAlgHom g.toAlgHom h'
  exact { F with
    map_mem := by
      apply gradedTensorLift_map_mem 𝒜 ℬ 𝒞
        (F := F) (f := f) (g := g)
      intro a b
      -- The local `F` is Mathlib's underlying lift; expose its stored factor maps to use its
      -- pure-tensor computation theorem.
      change F (a ᵍ⊗ₜ[R] b) = f.toAlgHom a * g.toAlgHom b
      exact GradedTensorProduct.lift_tmul 𝒜 ℬ f.toAlgHom g.toAlgHom h' a b }

end Lift
end TauCeti
end

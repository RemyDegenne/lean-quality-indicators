@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable (K : Type u) (Γ : Type v)

variable [CommRing K] [Fintype Γ] [Group Γ]

omit [Fintype Γ] in
@[simp]
lemma counitAlgHom_apply (f : FiniteGroupFunctions K Γ) :
    counitAlgHom K Γ f = f 1 := rfl

end FiniteGroupFunctions
end AlgebraicGeometry
end

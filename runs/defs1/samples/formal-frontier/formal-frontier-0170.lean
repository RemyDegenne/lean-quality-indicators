public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]
  (V : Type u) [AddCommGroup V] [Module K V]
  (W : Type u) [AddCommGroup W] [Module K W]

/-- The cone of genuine group morphisms onto the chosen basis coordinates. -/
@[expose] def vectorGroupBasisFan {i : Type u} (b : Module.Basis i K V) :
    Limits.Fan (fun _ : i ↦ additiveGroupScheme K) :=
  Limits.Fan.mk (vectorGroupScheme K V) (vectorGroupProjection K V b)

end AlgebraicGeometry
end
end

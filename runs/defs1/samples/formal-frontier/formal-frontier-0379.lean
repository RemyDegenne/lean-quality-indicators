public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The affine vector group scheme; its Hopf structure comes from the primitive
generators of the symmetric algebra. -/
abbrev vectorGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨vectorGroupUnderlyingScheme K V⟩

end AlgebraicGeometry
end
end

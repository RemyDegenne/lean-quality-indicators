@[expose] public section

noncomputable section

open CategoryTheory TensorProduct

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

section MatrixSchemeBasisChange

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (i j : Type u) [Fintype i] [Fintype j]
  [DecidableEq i] [DecidableEq j]
  (b : Module.Basis i K V) (c : Module.Basis j K V)

omit [FiniteDimensional K V] in
@[simp]
theorem endMatrixSchemeBasisChangeIso_refl :
    endMatrixSchemeBasisChangeIso K V i i b b =
      Iso.refl (vectorGroupScheme K (Matrix i i K)) := by
  simp [endMatrixSchemeBasisChangeIso]

end MatrixSchemeBasisChange
end AlgebraicGeometry
end
end

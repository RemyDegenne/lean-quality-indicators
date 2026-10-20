@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory GeneralLinearCoordinateRing
  SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The unit of `Gₘ` as an actual morphism from the trivial group scheme. -/
def multiplicativeUnitGroupHom :
    Grp.trivial (Over (Spec (.of K))) ⟶ multiplicativeGroupScheme K :=
  Grp.homMk' (0 : Mon.trivial (Over (Spec (.of K))) ⟶
    (multiplicativeGroupScheme K).toMon)

end AlgebraicGeometry
end
end

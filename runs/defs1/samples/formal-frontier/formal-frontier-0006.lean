@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

/-- Unique morphism to the trivial group object. -/
def unitriangularToTrivialGroupHom :
    unitriangularGroupScheme K n ⟶ Grp.trivial (Over (Spec (.of K))) :=
  Grp.homMk' (default : (unitriangularGroupScheme K n).toMon ⟶
    Mon.trivial (Over (Spec (.of K))))

end AlgebraicGeometry
end
end

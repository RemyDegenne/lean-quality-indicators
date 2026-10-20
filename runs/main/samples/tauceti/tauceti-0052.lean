public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R]

variable (X : Scheme.{u}) [X.Over (Spec (.of R))]

@[simp]
lemma FiniteLocallyFreeSheaf.relativeDifferentials_obj [Smooth (X ↘ Spec (.of R))] :
    (FiniteLocallyFreeSheaf.relativeDifferentials R X).obj = X.relativeDifferentials R :=
  (rfl)

end
end TauCeti.AlgebraicGeometry
end

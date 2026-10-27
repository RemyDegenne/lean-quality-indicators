public section

open CategoryTheory WithConv

open scoped Matrix

namespace TauCeti.TypeBSpinCarrier

universe u v

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The weight torus factored through the subgroup generated over `R`. -/
noncomputable def generatedWeightTorusCoordinateMap :
    generatedCoordinateHopfAlgebra n R ⟶
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin (n + 1)))).obj :=
  generatedCoordinateLift n R (.inr ())

end TauCeti.TypeBSpinCarrier
end

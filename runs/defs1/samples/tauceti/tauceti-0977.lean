public section

universe v

namespace TauCeti.TypeBSpinCarrier

open AlgebraicGeometry CategoryTheory

open TauCeti.UniversalEnvelopingAlgebra

open scoped CategoryTheory.MonObj

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

variable (n : ℕ)

/-- The split spin weight torus on matrix-valued carrier points. -/
noncomputable def weightTorusPoints (A : Type v) [CommRing A] :
    (Fin (n + 1) → Aˣ) →* points n A :=
  kostantToralWeightTorusPoints
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) A

end TauCeti.TypeBSpinCarrier
end

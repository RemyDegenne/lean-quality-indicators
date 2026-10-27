namespace P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic

set_option autoImplicit false

open scoped IntermediateField

namespace AlgExtSpread

p2m_reactivate

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

p2m_reactivate

section API

variable {k K : Type} [Field k] [Field K] [Algebra k K]

variable {X : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of k)}

noncomputable def proj (fX : X ⟶ Spec (CommRingCat.of k)) (L : FinIF k K) :
    pullback fX (gK k K) ⟶ (D k K X fX).obj (op L) :=
  (c k K X fX).π.app (op L)

end API
end AlgExtSpread
end P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic

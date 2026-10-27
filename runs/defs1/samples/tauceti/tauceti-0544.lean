public section

open CategoryTheory WithConv

namespace TauCeti

namespace GeneralLinear

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The determinant of the localized generic matrix, transported to the bundled coordinate
Hopf algebra of `GLₙ`, as a group-like element. -/
noncomputable def determinantGroupLike :
    _root_.GroupLike R (coordinateHopfAlgebra R n) where
  val := coordinateHopfAlgebraAlgEquiv R n
    (Matrix.det (localizedGenericMatrix R n))
  isGroupLikeElem_val := by
    constructor
    · rw [coordinateHopfAlgebra_counit_apply,
        counit_det_localizedGenericMatrix]
    · rw [coordinateHopfAlgebra_comul_apply,
        comul_det_localizedGenericMatrix]
      simp

end GeneralLinear
end TauCeti
end

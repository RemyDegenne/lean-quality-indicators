namespace P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

p2m_open

namespace VbUnrq

section Newton

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

variable (φ : F →ₐ[K] F') (W : Place K F') (m : Polynomial F) (z : F')

variable {φ W m z}

theorem eval_map_coe (mO : Polynomial W.toValuationSubring) (x : W.toValuationSubring) :
    ((mO.eval x : W.toValuationSubring) : F') = (mO.map W.toValuationSubring.subtype).eval (x : F') := by
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_hom W.toValuationSubring.subtype x).symm

end Newton
end VbUnrq
end P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst

namespace P2MW.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero

set_option autoImplicit false

open Polynomial IntermediateField

namespace ModularCurve

p2m_open

theorem map_eval₂_aeval_toRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (g : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (a b : A) :
    g (Φ.eval₂ (aeval (R := ℤ) a).toRingHom b) = Φ.eval₂ (aeval (R := ℤ) (g a)).toRingHom (g b) := by
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

end ModularCurve
end P2MW.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero

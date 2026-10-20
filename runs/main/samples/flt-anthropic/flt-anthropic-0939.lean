namespace P2MW.S_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top

set_option autoImplicit false

open AlgebraicCurve

namespace GluedGenAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (S : Finset (Place K F × Place K F)) (T₀ T₁ : Finset (Place K F))

theorem single_sub_single_mem_degZero (hdeg : ∀ v : Place K F, v.deg = 1) (P Q : Place K F) :
    Finsupp.single P (1 : ℤ) - Finsupp.single Q 1 ∈ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg P, hdeg Q, sub_self]

end GluedGenAux
end P2MW.S_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top

set_option autoImplicit false

open scoped NNReal

open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section Defects

variable [CompleteSpace K] {q u v w : K}

lemma pointX_inv_mul (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hdiv : OffLattice q (u * v⁻¹)) :
    pointX q (u⁻¹ * v) = pointX q (u * v⁻¹) := by
  rw [show u⁻¹ * v = (u * v⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv, mul_comm]]
  exact pointX_inv hq0 (mul_ne_zero hu0 (inv_ne_zero hv0)) hdiv

end Defects
end TateCurve

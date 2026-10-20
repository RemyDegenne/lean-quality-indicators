@[expose] public section

open CliffordAlgebra

namespace CliffordAlgebraQuaternion

open scoped Quaternion

open QuaternionAlgebra

variable {R : Type*} [CommRing R] (c₁ c₂ : R)

/-- The quaternion basis vectors within the algebra. -/
@[simps i j k]
def quaternionBasis : QuaternionAlgebra.Basis (CliffordAlgebra (Q c₁ c₂)) c₁ 0 c₂ where
  i := ι (Q c₁ c₂) (1, 0)
  j := ι (Q c₁ c₂) (0, 1)
  k := ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)
  i_mul_i := by
    rw [ι_sq_scalar, Q_apply, ← Algebra.algebraMap_eq_smul_one]
    simp
  j_mul_j := by
    rw [ι_sq_scalar, Q_apply, ← Algebra.algebraMap_eq_smul_one]
    simp
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul, zero_sub, eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, QuadraticMap.polar]
    simp

end CliffordAlgebraQuaternion
end

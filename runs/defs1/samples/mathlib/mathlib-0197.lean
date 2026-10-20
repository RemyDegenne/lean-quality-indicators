@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace NNReal

/-- Nonnegative real numbers `p q r : ℝ≥0` are said to be a **Hölder triple** if `p` and `q` are
positive and `p⁻¹ + q⁻¹ = r⁻¹`. -/
@[mk_iff]
structure HolderTriple (p q r : ℝ≥0) : Prop where
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
  left_pos : 0 < p
  right_pos : 0 < q

end NNReal
end
end

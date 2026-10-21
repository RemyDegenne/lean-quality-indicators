namespace OAI

noncomputable section

namespace CKSLorentz

noncomputable section

open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set

open scoped BigOperators

lemma bilinear_eq_of_coordinate_basis (B C : Point →L[ℝ] Point →L[ℝ] ℝ)
    (h : ∀ i j, B (basis i) (basis j) = C (basis i) (basis j)) : B = C := by
  ext v w
  rw [← sum_coordinate_basis v,← sum_coordinate_basis w]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,h]

end
end CKSLorentz
end
end OAI

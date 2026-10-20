public section

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℤ) [(W.baseChange ℚ).IsElliptic]

omit [(W.baseChange ℚ).IsElliptic] in
@[simp]
theorem mem_boundedIntegralSolutions_iff (B : ℕ) (p : ℤ × ℤ) :
    p ∈ W.boundedIntegralSolutions B ↔
      W.toAffine.Equation p.1 p.2 ∧ -(B : ℤ) ≤ p.1 ∧ p.1 ≤ B := by
  simp only [boundedIntegralSolutions, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨x, hx, y, _, hp⟩, heq⟩
    have hxy : p = (x, y) := hp.symm
    rcases hxy with rfl
    exact ⟨(W.toAffine.equation_iff _ _).2 heq, hx.1, hx.2⟩
  · rintro ⟨heq, hx₁, hx₂⟩
    have hy := W.abs_yCoord_le_integralYCoordBound heq
    have hy' : -(W.integralYCoordBound p.1 : ℤ) ≤ p.2 ∧
        p.2 ≤ W.integralYCoordBound p.1 := abs_le.mp hy
    exact ⟨⟨p.1, ⟨hx₁, hx₂⟩, p.2, hy', rfl⟩,
      (W.toAffine.equation_iff _ _).1 heq⟩

end WeierstrassCurve
end

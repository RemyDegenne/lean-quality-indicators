public section

open Module Matrix

namespace TauCeti.IntegralLattice

theorem hyperbolicPlane_binaryNormForm_primPart :
    (hyperbolicPlane.binaryNormForm hyperbolicPlaneBasis).primPart = ⟨0, 1, 0⟩ := by
  rw [hyperbolicPlane_binaryNormForm]
  ext <;> norm_num [BinaryQuadraticForm.primPart_a, BinaryQuadraticForm.primPart_b,
    BinaryQuadraticForm.primPart_c, BinaryQuadraticForm.content_def]

end TauCeti.IntegralLattice
end

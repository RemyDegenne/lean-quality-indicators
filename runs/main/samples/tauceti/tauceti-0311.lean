public section

noncomputable section

open MeasureTheory Measure UpperHalfPlane ModularGroup Complex Set ENNReal

open Matrix.SpecialLinearGroup

open scoped ComplexConjugate MatrixGroups ModularForm NNReal Pointwise

namespace UpperHalfPlane

@[simp]
theorem peterssonInner_conj_symm (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    conj (peterssonInner k D g f) = peterssonInner k D f g := by
  simp only [peterssonInner, ← integral_conj, petersson_symm k g f]

end UpperHalfPlane
end
end

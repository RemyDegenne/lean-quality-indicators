namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance pairSquareFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

@[simp] theorem fieldPairCoefficientMoment_zero {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    fieldPairCoefficientMoment g χ 0 = 0 := by
  simp [fieldPairCoefficientMoment, mellinCoefficient]

end Ostmann
end OAI

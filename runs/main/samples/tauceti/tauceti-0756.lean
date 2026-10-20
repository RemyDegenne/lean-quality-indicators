public noncomputable section

open LaurentPolynomial

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

theorem sigmaF_apply (a : ℂ[T;T⁻¹]) : sigmaF q a = rescale ℂ (Units.mk0 q Fact.out ^ 2) a :=
  (rfl)

end TauCeti.UqSl2
end

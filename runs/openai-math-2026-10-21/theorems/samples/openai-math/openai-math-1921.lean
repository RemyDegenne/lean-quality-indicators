namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial

open scoped BigOperators Topology ContDiff

open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem monomial_hasFDerivAt (k : ℕ × ℕ) (r : Plane) :
    HasFDerivAt (monomial k) (monomialDerivative k r) r := by
  have h := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x:=r)).pow k.1).mul
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x:=r)).pow k.2)
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [monomialDerivative]
  ring

end PackingSufficiencySupport.FiniteMoment.Radial
end
end OAI

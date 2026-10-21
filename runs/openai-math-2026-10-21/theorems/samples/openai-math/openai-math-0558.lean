namespace OAI

section

noncomputable section

open scoped BigOperators Matrix MatrixOrder Topology

open MeasureTheory Real Matrix

namespace SKRatio.Observation

open Calculus Fields

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma history_endpoint_product (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (h₀ : Fin n → ℝ) {N : ℕ} (hN : 0<N) (h : History n N) :
    History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h =
      productPrior (fun i => fieldPrior (observedField g (N:ℝ)⁻¹ h₀ h i)) := by
  rw [history_posterior_gibbs g hg, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'),
    sub_self,zero_scale_product]

end SKRatio.Observation
end
end
end OAI

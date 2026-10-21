namespace OAI

section

noncomputable section

open MvPowerSeries

open scoped Classical

open scoped TensorProduct

open IsLocalRing

open MvPowerSeries IsLocalRing

open scoped ENNReal

open scoped ENNReal TensorProduct Classical DirectSum

open TensorProduct

open scoped TensorProduct nonZeroDivisors

open scoped nonZeroDivisors

open scoped BigOperators

open scoped nonZeroDivisors TensorProduct

open scoped Classical Pointwise

open CategoryTheory CategoryTheory.Limits

open CochainComplex CochainComplex.HomComplex

open scoped ENNReal ZeroObject

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

open CategoryTheory

namespace Lech.Normalization

open IsLocalRing MvPowerSeries

variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
lemma parameter_eval_injective (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D)
    (hdim : (Fintype.card σ : WithBot ℕ∞) ≤ ringKrullDim D) :
    Function.Injective (Lech.PowerSeries.eval φ (maximalIdeal D) z hz) := by
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra (MvPowerSeries σ k) D := ψ.toAlgebra
  let : Module.Finite (MvPowerSeries σ k) D := finite_parameter_algebra φ hφ z hz hprim
  exact injective_of_integral_dimension ψ (Algebra.IsIntegral.isIntegral)
    hdim (Lech.PowerSeries.dimension_le_variables σ k)

end Lech.Normalization
end
end
end OAI

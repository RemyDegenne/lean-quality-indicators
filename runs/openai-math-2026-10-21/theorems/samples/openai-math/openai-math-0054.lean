namespace OAI

noncomputable section

namespace ZeroKey

section

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ProbabilityTheory ENNReal NNReal Topology

universe v4526_0

universe v4553_0

universe v4584_0 v4584_1

variable {Ω : Type v4584_0} {ι : Type v4584_1} [inst4584_0 : MeasurableSpace Ω] [inst4584_1 : Fintype ι] [inst4584_2 : DecidableEq ι]
  {μ : Measure Ω} {G : Ω → Matrix ι ι ℂ}

lemma integrable_matrix_of_entries (hG : ∀ i j, Integrable (fun ω => G ω i j) μ) :
    Integrable G μ := by
  have h : Integrable (fun ω i j => G ω i j) μ :=
    integrable_pi_iff.mpr (fun i => integrable_pi_iff.mpr (hG i))
  let L : (ι → ι → ℂ) →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℂ).toLinearMap
  exact L.integrable_comp h

end
end ZeroKey
end
end OAI

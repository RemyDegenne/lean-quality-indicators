namespace OAI

noncomputable section

open scoped TensorProduct InnerProductSpace ComplexOrder

open ContinuousLinearMap UniformSpace

namespace SecretKey

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {ι κ : Type*}

lemma tensor_positive_trace (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    (hA : HasFinitePositiveTrace b A) (hB : HasFinitePositiveTrace c B) :
    HasFinitePositiveTrace (tensorHilbertBasis b c) (hilbertTensorMap A B) ∧
      hilbertTrace (tensorHilbertBasis b c) (hilbertTensorMap A B)=hilbertTrace b A*hilbertTrace c B := by
  have hnA (i : ι) : 0≤(inner ℂ (b i) (A (b i))).re :=
    (nonneg_iff_isPositive.mp hA.1).re_inner_nonneg_right _
  have hnB (j : κ) : 0≤(inner ℂ (c j) (B (c j))).re :=
    (nonneg_iff_isPositive.mp hB.1).re_inner_nonneg_right _
  have hs := hA.2.mul_of_nonneg hB.2 hnA hnB
  refine ⟨⟨hilbertTensorMap_nonneg hA.1 hB.1,?_⟩,?_⟩
  · exact hs.congr (fun p => (tensor_positive_diagonal b c hA.1 hB.1 p).symm)
  · unfold hilbertTrace
    simp_rw [tensor_positive_diagonal b c hA.1 hB.1]
    exact (hA.2.tsum_mul_tsum hB.2 hs).symm

end SecretKey
end
end OAI

namespace OAI

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold ContDiff

attribute [local instance] factorExtensionTopology

variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (R : NonabelianFactorSystem L (IntegralLatticeGroup n))
  (C : NilpotentKernelCompletion (FactorExtension.inl R))
  (π : C.carrier →* AbelianRealSpace n)
  (hπ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ π)
  (he : ∀ a, π (C.embed a) = integralRealHeight a.right)

local instance completionEmbeddingTopologicalGroup : IsTopologicalGroup C.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, C.carrier)) ⊤

theorem completion_factorization (a : FactorExtension R) :
    C.embed a = C.embed (FactorExtension.inl R a.left) *
      C.embed (⟨1, a.right⟩ : FactorExtension R) := by
  rw [← map_mul]
  apply congrArg C.embed
  apply FactorExtension.ext
  · change a.left = a.left * R.action 1 1 * R.factor 1 a.right
    rw [map_one, R.factor_one_left, mul_one, mul_one]
  · exact (one_mul _).symm

end PolycyclicRecognition
end
end OAI

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

open scoped InnerProductSpace

open scoped TensorProduct

open scoped TensorProduct InnerProductSpace Topology

open UniformSpace Completion Filter

open scoped TensorProduct

open UniformSpace Completion

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.FreeMoments

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable {S τ}

variable (hstar : ∀ a : A, τ (star a) = star (τ a))

variable (h1 : τ 1 = 1)

include hstar h1 in
lemma generator_le_reducedAlgebra (i : ι) : S i ≤ reducedAlgebra S hstar h1 :=
  fun a ha => generator_mem_wordSpan h1 i a ha

end Kadison.FreeMoments
end
end OAI

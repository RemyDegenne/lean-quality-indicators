namespace OAI

noncomputable section

open scoped BigOperators

namespace PD4Tensor.FrobeniusTruncation

noncomputable section

open scoped TensorProduct

variable (K σ : Type*) [Field K] (p : ℕ)

variable {K σ p} {B : Type*} [CommRing B] [Algebra K B]

@[ext] theorem hom_ext {f g : Ring K σ p →ₐ[K] B}
    (h : ∀ i, f (coord K σ p i)=g (coord K σ p i)) : f=g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

end
end PD4Tensor.FrobeniusTruncation
end
end OAI

namespace OAI

noncomputable section

open scoped BigOperators

namespace PD4Tensor

namespace FrobeniusTruncation

noncomputable section

variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)

variable [CharP K p]

variable [Fact p.Prime]

theorem top_product_eq_socle (f : σ → MvPolynomial σ K)
    (hf : ∀ i, MvPolynomial.constantCoeff (f i) = 0) :
    (∏ i : σ, Ideal.Quotient.mk (ideal K σ p) (f i) ^ (p-1)) =
      (tangentMatrix K σ f).det ^ (p-1) • socle K σ p := by
  rw [top_product_eq_linear K σ p f hf]
  have hsub : (∏ i : σ, Ideal.Quotient.mk (ideal K σ p) (linearPart K σ (f i)) ^ (p-1)) =
      linearSubst K σ p (tangentMatrix K σ f) (socle K σ p) := by
    simp only [socle, map_prod, map_pow]
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    change Ideal.Quotient.mk (ideal K σ p) (linearPart K σ (f i)) =
      MvPolynomial.aeval (fun j => Ideal.Quotient.mk (ideal K σ p)
        (linearForm K σ (tangentMatrix K σ f) j)) (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X]
    rfl
  rw [hsub, linearSubst_socle]

end
end FrobeniusTruncation
end PD4Tensor
end
end OAI

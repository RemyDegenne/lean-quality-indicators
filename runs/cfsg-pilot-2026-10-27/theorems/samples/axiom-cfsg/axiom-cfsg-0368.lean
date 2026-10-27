public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

open CatalogueBOrthogonalScalarSquare

universe u v

variable {K : Type u} [Field K] [Finite K] {V : Type v}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem odd_orthogonal_linear_involution_fixed_p_components
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card K = ℓ ^ f) (hn : 2 ≤ Module.finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (orthogonalOperatorCentralizer Q A.toLinearMap),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (projectiveConjugation Q A μ hsim)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L) := by
  constructor
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact original_centralizer_pComponent_quasisimple ℓ f hℓ hodd hf hcard hn Q hQ
      A d μ hsquare hsim hnonscalar p L hL
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact projective_fixed_pComponent_quasisimple ℓ f hℓ hodd hf hcard hn Q hQ
      A d μ hsquare hsim hnonscalar p L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
end

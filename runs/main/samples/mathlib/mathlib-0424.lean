@[expose] public section

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

section Map

variable (f : R →+* S₁)

theorem eval₂_comp (f : R →+* S₁) (g : σ → R) (p : MvPolynomial σ R) :
    f (eval g p) = eval₂ f (f ∘ g) p := by
  rw [← p.map_id, eval_map, eval₂_comp_right]

end Map
end CommSemiring
end MvPolynomial
end
end

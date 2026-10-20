public section

universe u v w

namespace TauCeti.Algebra

variable {R : Type u} {M : Type v} {A : Type w}

variable [CommSemiring R] [Semiring A] [_root_.Algebra R A] [AddCommMonoid M] [Module R M]

theorem wordFiltration_eq_pow (f : M →ₗ[R] A) (k : ℕ) :
    wordFiltration f k = (1 ⊔ LinearMap.range f) ^ k :=
  (rfl)

end TauCeti.Algebra
end

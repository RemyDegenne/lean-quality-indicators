public section

noncomputable section

universe u v v' v''

variable {K : Type u} {V V₁ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}

open Cardinal Submodule Function Set

namespace LinearMap

section Semiring

variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid V₁] [Module K V₁]

variable [AddCommMonoid V'] [Module K V']

theorem rank_le_range (f : V →ₗ[K] V') : rank f ≤ Module.rank K V' :=
  Submodule.rank_le _

end Semiring
end LinearMap
end
end

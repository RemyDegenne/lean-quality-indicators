public section

open scoped DirectSum

namespace TauCeti

universe u v w

variable {ι : Type v} [DecidableEq ι]

section Restriction

variable {R : Type u} [Semiring R] (M : ι → Type w)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

@[simp]
theorem DirectSum.componentLinearEquiv_apply (d : ι) (hd : ∀ i, i ≠ d → Subsingleton (M i))
    (x : ⨁ i, M i) :
    DirectSum.componentLinearEquiv (R := R) M d hd x = DirectSum.component R ι M d x :=
  (rfl)

end Restriction
end TauCeti
end

public section

namespace TauCeti

universe u v

section Semiring

variable {A : Type u} [Semiring A] {e : A}

/-- An idempotent of a semiring is **primitive** when it is nonzero and is not the sum of two
nonzero orthogonal idempotents. -/
structure IsPrimitiveIdempotent (e : A) : Prop where
  /-- A primitive idempotent is an idempotent. -/
  isIdempotentElem : IsIdempotentElem e
  /-- A primitive idempotent is nonzero; without this `0` would be primitive in every ring. -/
  ne_zero : e ≠ 0
  /-- A primitive idempotent does not split: in every decomposition of it into two orthogonal
  idempotents one of the summands vanishes. -/
  eq_zero_or_eq_zero_of_add {e₁ e₂ : A} (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂)
    (h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0) (hsum : e₁ + e₂ = e) : e₁ = 0 ∨ e₂ = 0

end Semiring
end TauCeti
end

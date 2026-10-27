@[expose] public section

open Function

section Variants

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (M N)

/-- `Covariant` is useful to formulate succinctly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `CovariantClass` doc-string for its meaning. -/
def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

end Variants
end

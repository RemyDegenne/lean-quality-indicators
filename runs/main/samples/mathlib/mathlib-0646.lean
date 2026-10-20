@[expose] public section

variable {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

namespace Pi

notation3 (prettyPrint := false) "Πₗ " (...) ", " r:(scoped p => Lex (∀ i, p i)) => r

set_option backward.isDefEq.respectTransparency false in
theorem colex_le_iff_of_unique [Unique ι] [LinearOrder ι] [∀ i, PartialOrder (β i)]
    {x y : Colex (∀ i, β i)} : x ≤ y ↔ x default ≤ y default := by
  simp_rw [le_iff_lt_or_eq, Pi.Colex.lt_iff_of_unique, ← ofColex_inj, funext_iff, Unique.forall_iff,
    ofColex_apply]

end Pi
end

@[expose] public section

variable {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

namespace Pi

notation3 (prettyPrint := false) "Πₗ " (...) ", " r:(scoped p => Lex (∀ i, p i)) => r

theorem Lex.lt_iff_of_unique [Unique ι] [∀ i, LT (β i)] [Preorder ι] {x y : Lex (∀ i, β i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

end Pi
end

@[expose] public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

theorem ordinary_iff_separating [Countable α] [Infinite α]
    (H : Generic.LanguageClass α) (hUUS : Generic.UUS H) :
    Generic.GeneratableInLimit H ↔
      ∃ T : Generic.Language α → Finset α,
        (∀ L, L ∈ H → (↑(T L) : Set α) ⊆ L) ∧ Separates H T :=
  (ordinary_iff_finiteWitnesses H hUUS).trans (finiteWitnesses_iff_separating H)

end GenLimit.FiniteWitness
end

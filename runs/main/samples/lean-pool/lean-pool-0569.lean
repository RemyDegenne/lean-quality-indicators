@[expose] public section

open scoped BigOperators

open scoped FinsetFamily

open Finset

open Finset.Colex

namespace BooleanIsoperimetry

lemma neighborhood_union {N r : ℕ} (A B : Finset (Cube N)) :
    neighborhood r (A ∪ B) = neighborhood r A ∪ neighborhood r B := by
  ext x
  simp [mem_neighborhood_iff, or_and_right, exists_or]

end BooleanIsoperimetry
end

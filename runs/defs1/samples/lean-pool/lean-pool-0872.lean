@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The ordered finite simplex in `Fin n` coordinates, including the ambient
closed cube bounds.  This is the coordinate target for arbitrary canonical
orders.
-/
def orderedFinSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {ts | (∀ i, 0 ≤ ts i ∧ ts i ≤ 1) ∧
    OrderedSimplexParams 1 (List.ofFn ts)}

end Forest
end BKAR
end
end

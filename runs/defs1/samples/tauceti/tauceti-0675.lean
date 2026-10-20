public section

noncomputable section

open NumberField NumberField.InfinitePlace

universe u v v'

namespace QuadraticForm

variable {K : Type u} [Field K]

variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The negative index of a quadratic form at a real place. -/
def realNegativeIndex (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) : ℕ :=
  (Q.realSignature w).2

end QuadraticForm
end
end

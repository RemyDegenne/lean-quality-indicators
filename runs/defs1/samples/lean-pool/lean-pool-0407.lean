@[expose] public section

namespace LeanPool.Monsky

noncomputable section

open ValuationSubring

open Algebra

open Polynomial

/-- The set of subrings of `ℝ` not containing `1/2`. -/
def S := {A : Subring ℝ | (1/2) ∉ A}

end
end LeanPool.Monsky
end

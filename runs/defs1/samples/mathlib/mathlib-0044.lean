@[expose] public section

open WithZero

noncomputable section

open Nat padicNorm CauSeq CauSeq.Completion Metric

notation "ℚ_[" p "]" => Padic p

namespace Padic

variable {p : ℕ} [hp : Fact p.Prime]

open Filter Set

open WithZero

/-- The additive `p`-adic valuation on `ℚ_[p]`, as an `addValuation`. -/
def addValuation : AddValuation ℚ_[p] (WithTop ℤ) :=
  AddValuation.of addValuationDef AddValuation.map_zero AddValuation.map_one AddValuation.map_add
    AddValuation.map_mul

end Padic
end
end

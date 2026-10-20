@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open MarkedGraphs.Certificate

open Utilities.Certificate

open Utilities.Certificate.ContractionForestCensusGeneral

namespace RichWitness

variable {m n p : ℕ}

/-- The firing script denoted by the decoded rich block data. -/
noncomputable def richCensusPiecewiseScript (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hx : Γ.Holds x) (ℓ : Fin p → ℕ)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = ℓ e)
    (hn : 0 < n) (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (a : Fin n) :
    firingScript (censusSpec core hn ℓ hForest hNotLoopy).graph :=
  (censusSpec core hn ℓ hForest hNotLoopy).piecewiseScript
    (w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn hForest hNotLoopy a)

end RichWitness
end Utilities.Subdivision.ClosedRowProof
end

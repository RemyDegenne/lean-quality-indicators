namespace OAI

namespace MatroidProphet.General

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {R : Type*} [MeasurableSpace R]

lemma reward_nonneg (A : OnlineRule n R) (r : R) (s v : Weights n)
    (π : ArrivalOrder n) (hv : ∀ e, 0 ≤ v e) : 0 ≤ reward A r s v π :=
  Finset.sum_nonneg fun e _ => hv e

end MatroidProphet.General
end OAI

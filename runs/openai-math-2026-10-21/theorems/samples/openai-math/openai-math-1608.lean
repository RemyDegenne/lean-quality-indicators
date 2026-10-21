namespace OAI

open MeasureTheory Finset

namespace MatroidProphet

variable {n : ℕ} {Q : Type*} [MeasurableSpace Q]

lemma secretaryDecisionAt_congr (A : SecretaryRule n Q) (q : Q)
    (w w' : Weights n) (π π' : ArrivalOrder n) (k : Fin n)
    (hh : history w π k = history w' π' k) :
    secretaryDecisionAt A q w π k = secretaryDecisionAt A q w' π' k := by
  simp only [secretaryDecisionAt, hh]

end MatroidProphet
end OAI

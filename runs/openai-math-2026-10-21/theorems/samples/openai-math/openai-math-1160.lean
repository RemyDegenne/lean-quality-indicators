namespace OAI

section

open MeasureTheory ProbabilityTheory

open scoped BigOperators NNReal

open MeasureTheory ProbabilityTheory

open scoped BigOperators NNReal

open scoped BigOperators

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

section SharedHitGeometry

open scoped Classical

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

omit [Fintype V] [DecidableEq V] [Fintype D] in
lemma terminal_low_loss (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : V) (hanchor : touchedToEncoded s hit E v = ∅) :
    (batchesOn hit (touchedToEncoded s hit E v)).card = 0 := by
  simp [hanchor, batchesOn]

end SharedHitGeometry
end SharpRamseyFive.ResidualCertificate
end
end OAI

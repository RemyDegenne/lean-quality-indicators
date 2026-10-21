namespace OAI

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Set

open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree

open PrimeDegreePackets

@[simp]
lemma matrixEuclideanEquiv_symm_apply (n : ℕ)
    (V : Matrix (Fin n) (Fin n) ℝ) (p : Fin n × Fin n) :
    (matrixEuclideanEquiv n).symm V p = V p.1 p.2 := rfl

end DukePrimeDegree
end
end OAI

@[expose] public section

open scoped BigOperators Topology

open Filter MeasureTheory

namespace CKN.Foundation.Harmonic.Commutator

noncomputable section

/-- The third derivative of the inverse Euclidean radius, in the convention
used by the Newtonian kernel. -/
def inverseThirdFormula (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -15 * x m * x j * x l * (CKN.vecEuclideanNorm x ^ 7)⁻¹ +
    3 * ((if m = l then 1 else 0) * x j +
      (if m = j then 1 else 0) * x l +
      (if l = j then 1 else 0) * x m) *
      (CKN.vecEuclideanNorm x ^ 5)⁻¹

end
end CKN.Foundation.Harmonic.Commutator
end

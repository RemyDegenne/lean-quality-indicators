namespace OAI

noncomputable section

namespace ContinuumCoulomb.OccupationFock

open Laughlin.Fock SlaterOccupation HubbardGlobal

open scoped BigOperators

variable {Q n : ℕ}

lemma vector_support (c : EuclideanSpace ℂ (Occupied Q n))
    (A : Finset (Fin (Q + 1))) (hA : A.card ≠ n) : (fockBasis Q).repr (vector c) A = 0 := by
  rw [← fockCoordinates_apply, vector_coordinates]
  apply coordinateInclusion_apply_outside _ c A
  intro S he
  apply hA
  rw [← he]
  exact S.property

end ContinuumCoulomb.OccupationFock
end
end OAI

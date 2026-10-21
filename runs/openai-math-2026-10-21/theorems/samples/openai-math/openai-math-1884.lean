namespace OAI

noncomputable section

open scoped ComplexConjugate ENNReal Classical

open scoped ComplexConjugate BigOperators

namespace Heisenberg

lemma nearestNeighbor_symm {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    NearestNeighbor y x := by
  unfold NearestNeighbor at *
  simpa only [abs_sub_comm] using h

end Heisenberg
end
end OAI

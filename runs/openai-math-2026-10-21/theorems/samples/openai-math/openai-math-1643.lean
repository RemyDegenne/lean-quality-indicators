namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

lemma comparisonMass_partition (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) :
    comparisonMass M a H =
      ∑ i ∈ trueLevels M a H, weightBase ^ i *
        (((positiveGreedy M a \ H).filter (fun e => a e = some i)).card : ℝ) := by
  exact (sum_weightGroups_mass a _ _
    (weightLevels_mono a (positiveGreedy_survivors_subset M a H)) weightBase).symm

end MatroidProphet.MainAlgorithm
end OAI

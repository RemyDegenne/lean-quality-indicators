namespace OAI

noncomputable section

open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma binarySweep_zero (d : ℕ) : binarySweep d (fun _ _ => false) = 1 := by
  simp [binarySweep, coordinateLayer_zero, List.ofFn_const]

end BinaryCoordinateSweeps
end
end OAI

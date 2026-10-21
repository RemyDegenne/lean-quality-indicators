namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1463 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1463 = Sparse.eval value1463 (momentVector H) := by
  have heq : pivotMatrix1463 = (fun u v => node1463 (pivotPermutation1463 u) v) := by apply Matrix.ext; unfold pivotMatrix1463 node1463 pivotPermutation1463; decide +kernel
  have hmoment : injectiveMoment H node1463 = injectiveMoment H pivotMatrix1463 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1463 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1463 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1463 (0 : Fin 4)) =
      Sparse.eval value1035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1463 (0 : Fin 4) = raw1231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1463 raw1231; decide +kernel
    rw [heq]
    exact (canonical1231 hH).trans (sound1035 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1463 (1 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1463 (1 : Fin 4) = raw1121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1463 raw1121; decide +kernel
    rw [heq]
    exact (canonical1121 hH).trans (sound1031 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1463 (2 : Fin 4)) =
      Sparse.eval value400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1463 (2 : Fin 4) = raw1107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1463 raw1107; decide +kernel
    rw [heq]
    exact (canonical1107 hH).trans (sound400 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1463 (3 : Fin 4)) =
      Sparse.eval value1034 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1463 (3 : Fin 4) = raw1104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1463 raw1104; decide +kernel
    rw [heq]
    exact (canonical1104 hH).trans (sound1034 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1463 + (injectiveMoment H (mergeFirst pivotMatrix1463 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1463 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1463 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1463 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1463, value1031, value1034, value1035, value400, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics
end OAI

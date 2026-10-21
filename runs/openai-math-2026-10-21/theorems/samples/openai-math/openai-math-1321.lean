namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2023 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2023 = Sparse.eval value2023 (momentVector H) := by
  have heq : pivotMatrix2023 = (fun u v => node2023 (pivotPermutation2023 u) v) := by apply Matrix.ext; unfold pivotMatrix2023 node2023 pivotPermutation2023; decide +kernel
  have hmoment : injectiveMoment H node2023 = injectiveMoment H pivotMatrix2023 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2023 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2023 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2023 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2023 (0 : Fin 4) = raw6415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2023 raw6415; decide +kernel
    rw [heq]
    exact (canonical6415 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2023 (1 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2023 (1 : Fin 4) = raw3636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2023 raw3636; decide +kernel
    rw [heq]
    exact (canonical3636 hH).trans (sound1010 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2023 (2 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2023 (2 : Fin 4) = raw3424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2023 raw3424; decide +kernel
    rw [heq]
    exact (canonical3424 hH).trans (sound1000 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2023 (3 : Fin 4)) =
      Sparse.eval value609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2023 (3 : Fin 4) = raw3418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2023 raw3418; decide +kernel
    rw [heq]
    exact (canonical3418 hH).trans (sound609 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2023 + (injectiveMoment H (mergeFirst pivotMatrix2023 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2023 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2023 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2023 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2023, value1000, value1009, value1010, value609, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics
end OAI

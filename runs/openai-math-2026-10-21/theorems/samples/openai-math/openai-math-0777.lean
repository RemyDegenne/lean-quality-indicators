namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1684 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1684 = Sparse.eval value1684 (momentVector H) := by
  have heq : pivotMatrix1684 = (fun u v => node1684 (pivotPermutation1684 u) v) := by apply Matrix.ext; unfold pivotMatrix1684 node1684 pivotPermutation1684; decide +kernel
  have hmoment : injectiveMoment H node1684 = injectiveMoment H pivotMatrix1684 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1684 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1684 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1684 (0 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1684 (0 : Fin 4) = raw2455 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1684 raw2455; decide +kernel
    rw [heq]
    exact (canonical2455 hH).trans (sound842 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1684 (1 : Fin 4)) =
      Sparse.eval value489 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1684 (1 : Fin 4) = raw2079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1684 raw2079; decide +kernel
    rw [heq]
    exact (canonical2079 hH).trans (sound489 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1684 (2 : Fin 4)) =
      Sparse.eval value726 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1684 (2 : Fin 4) = raw2067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1684 raw2067; decide +kernel
    rw [heq]
    exact (canonical2067 hH).trans (sound726 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1684 (3 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1684 (3 : Fin 4) = raw2063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1684 raw2063; decide +kernel
    rw [heq]
    exact (canonical2063 hH).trans (sound805 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1684 + (injectiveMoment H (mergeFirst pivotMatrix1684 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1684 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1684 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1684 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1684, value489, value726, value805, value842, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics
end OAI

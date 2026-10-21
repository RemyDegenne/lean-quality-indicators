namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1841 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1841 = Sparse.eval value1841 (momentVector H) := by
  have heq : pivotMatrix1841 = (fun u v => node1841 (pivotPermutation1841 u) v) := by apply Matrix.ext; unfold pivotMatrix1841 node1841 pivotPermutation1841; decide +kernel
  have hmoment : injectiveMoment H node1841 = injectiveMoment H pivotMatrix1841 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1841 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1841 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1841 (0 : Fin 4)) =
      Sparse.eval value1084 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1841 (0 : Fin 4) = raw1295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1841 raw1295; decide +kernel
    rw [heq]
    exact (canonical1295 hH).trans (sound1084 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1841 (1 : Fin 4)) =
      Sparse.eval value522 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1841 (1 : Fin 4) = raw2547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1841 raw2547; decide +kernel
    rw [heq]
    exact (canonical2547 hH).trans (sound522 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1841 (2 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1841 (2 : Fin 4) = raw2586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1841 raw2586; decide +kernel
    rw [heq]
    exact (canonical2586 hH).trans (sound1047 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1841 (3 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1841 (3 : Fin 4) = raw2587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1841 raw2587; decide +kernel
    rw [heq]
    exact (canonical2587 hH).trans (sound1260 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1841 + (injectiveMoment H (mergeFirst pivotMatrix1841 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1841 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1841 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1841 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1841, value1047, value1084, value1260, value522, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics
end OAI

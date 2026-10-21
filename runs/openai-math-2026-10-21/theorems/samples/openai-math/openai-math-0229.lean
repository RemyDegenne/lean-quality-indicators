namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2317 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2317 = Sparse.eval value2317 (momentVector H) := by
  have heq : pivotMatrix2317 = (fun u v => node2317 (pivotPermutation2317 u) v) := by apply Matrix.ext; unfold pivotMatrix2317 node2317 pivotPermutation2317; decide +kernel
  have hmoment : injectiveMoment H node2317 = injectiveMoment H pivotMatrix2317 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2317 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2317 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2317 (0 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2317 (0 : Fin 4) = raw4674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2317 raw4674; decide +kernel
    rw [heq]
    exact (canonical4674 hH).trans (sound454 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2317 (1 : Fin 4)) =
      Sparse.eval value693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2317 (1 : Fin 4) = raw5002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2317 raw5002; decide +kernel
    rw [heq]
    exact (canonical5002 hH).trans (sound693 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2317 (2 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2317 (2 : Fin 4) = raw5012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2317 raw5012; decide +kernel
    rw [heq]
    exact (canonical5012 hH).trans (sound585 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2317 (3 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2317 (3 : Fin 4) = raw5013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2317 raw5013; decide +kernel
    rw [heq]
    exact (canonical5013 hH).trans (sound477 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2317 + (injectiveMoment H (mergeFirst pivotMatrix2317 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2317 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2317 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2317 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2317, value454, value477, value585, value693, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics
end OAI

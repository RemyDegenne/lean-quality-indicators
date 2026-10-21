namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound646 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node646 = Sparse.eval value646 (momentVector H) := by
  have heq : pivotMatrix646 = (fun u v => node646 (pivotPermutation646 u) v) := by apply Matrix.ext; unfold pivotMatrix646 node646 pivotPermutation646; decide +kernel
  have hmoment : injectiveMoment H node646 = injectiveMoment H pivotMatrix646 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix646 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix646 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix646 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix646 (0 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix646 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix646 (1 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix646 (1 : Fin 4) = raw4089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix646 raw4089; decide +kernel
    rw [heq]
    exact (canonical4089 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix646 (2 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix646 (2 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix646 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix646 (3 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix646 (3 : Fin 4) = raw4043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix646 raw4043; decide +kernel
    rw [heq]
    exact (canonical4043 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node646 + (injectiveMoment H (mergeFirst pivotMatrix646 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix646 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix646 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix646 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value646, value169, value202, value210, value284, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics
end OAI

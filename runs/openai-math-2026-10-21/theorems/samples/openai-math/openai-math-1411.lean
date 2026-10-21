namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound643 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node643 = Sparse.eval value643 (momentVector H) := by
  have heq : pivotMatrix643 = (fun u v => node643 (pivotPermutation643 u) v) := by apply Matrix.ext; unfold pivotMatrix643 node643 pivotPermutation643; decide +kernel
  have hmoment : injectiveMoment H node643 = injectiveMoment H pivotMatrix643 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix643 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix643 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix643 (0 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix643 (0 : Fin 4) = raw4920 := by apply Matrix.ext; unfold mergeFirst pivotMatrix643 raw4920; decide +kernel
    rw [heq]
    exact (canonical4920 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix643 (1 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix643 (1 : Fin 4) = raw4082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix643 raw4082; decide +kernel
    rw [heq]
    exact (canonical4082 hH).trans (sound204 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix643 (2 : Fin 4)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix643 (2 : Fin 4) = raw4040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix643 raw4040; decide +kernel
    rw [heq]
    exact (canonical4040 hH).trans (sound199 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix643 (3 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix643 (3 : Fin 4) = raw4037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix643 raw4037; decide +kernel
    rw [heq]
    exact (canonical4037 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node643 + (injectiveMoment H (mergeFirst pivotMatrix643 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix643 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix643 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix643 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value643, value198, value199, value204, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics
end OAI

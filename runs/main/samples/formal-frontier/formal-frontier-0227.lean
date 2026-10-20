set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace Bass

universe u

@[simp]
theorem coefficientRowKernelEquivTwo_symm_apply (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) (t : R) :
    ((coefficientRowKernelEquivTwo R a b h).symm t).1 =
      ![-a 1 * t, a 0 * t] := by
  have hval : ((coefficientRowKernelEquivTwo R a b h).symm t).1 =
      (LinearEquiv.coefficientRowCompletionTwo R a b h).symm ![0, t] := by
    change (LinearEquiv.coefficientRowCompletionTwo R a b h).symm
      ((kernelProjZeroEquiv R).symm t).1 = _
    rw [kernelProjZeroEquiv_symm_apply]
  rw [hval]
  ext i
  fin_cases i
  · simp
  · simp

end Bass
end

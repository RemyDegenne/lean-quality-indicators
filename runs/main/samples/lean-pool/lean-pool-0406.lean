open Complex Set

@[expose] public noncomputable section

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

@[simp] theorem carlsonLCoeff_one (t : ℂ) : carlsonLCoeff 1 t = 1 := by
  simp [carlsonLCoeff, iteratedDeriv_succ,
    (hasDerivAt_carlsonLKernel t one_mem_slitPlane).deriv, carlsonLKernel]

end DirichletTransform
end

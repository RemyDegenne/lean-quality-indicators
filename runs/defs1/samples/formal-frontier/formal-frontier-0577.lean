public section

noncomputable section

open Polynomial

open scoped TensorProduct

namespace Module.FiniteProjective

universe uR uS uM uN uL

variable (R : Type uR) (M : Type uM)
  [CommRing R] [AddCommGroup M] [Module R M]

section FreeComparison

variable {R : Type uR} {M : Type uM}
  [CommRing R] [AddCommGroup M] [Module R M]

/-- The split presentation associated to a finite basis. -/
@[expose] noncomputable def FreePresentation.ofBasis {n : ℕ}
    (b : Module.Basis (Fin n) R M) : FreePresentation R M where
  n := n
  proj := b.equivFun.symm.toLinearMap
  incl := b.equivFun.toLinearMap
  proj_comp_incl := by simp

end FreeComparison
end Module.FiniteProjective
end
end

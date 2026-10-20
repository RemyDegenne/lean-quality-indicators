@[expose] public section

open CategoryTheory

universe u v w

variable (R : Type u) [Ring R] (ι : Type v) [Fintype ι] [DecidableEq ι]

namespace KTheory

variable [Nonempty ι]

namespace K0

theorem matrixEquiv_symm_regular :
    (matrixEquiv R ι).symm (of (Matrix ι ι R) (Matrix ι ι R)) =
      of R (ι → R) := by
  apply (matrixEquiv R ι).injective
  rw [AddEquiv.apply_symm_apply]
  -- Evaluate the whole completion square at the inverse regular class.
  -- Only the additive equivalence is cancelled, not the class-to-K₀ map.
  have h := DFunLike.congr_fun (matrixEquiv_comp_ofClass R ι)
    ((ProjectiveClass.matrixEquiv R ι).symm
      (ProjectiveClass.of (Matrix ι ι R) (Matrix ι ι R)))
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at h
  -- Cancel the outer class round trip before normalizing the inverse class.
  rw [AddEquiv.apply_symm_apply] at h
  simpa only [ProjectiveClass.matrixEquiv_symm_regular, ofClass_of] using h.symm

end K0
end KTheory
end

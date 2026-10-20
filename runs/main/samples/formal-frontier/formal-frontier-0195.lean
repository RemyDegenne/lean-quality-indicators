@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

theorem indDualRealizationHomEquiv_symm_apply_comp_π
    (Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ)
    (g : indDualRealization.obj Q ⟶ indDualRealization.obj R)
    (j : R.unop.presentation.Iᵒᵖ) :
    indDualRealization.map ((indDualRealizationHomEquiv Q R).symm g) ≫
        (indDualPresentationCone R).π.app j =
      g ≫ (indDualPresentationCone R).π.app j := by
  rw [← indDualRealizationHomEquiv_apply,
    (indDualRealizationHomEquiv Q R).apply_symm_apply]

end Profinite
end

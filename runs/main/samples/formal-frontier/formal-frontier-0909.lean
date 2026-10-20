public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)

theorem basicTensorEquiv_symm_restriction {f g : R}
    (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f)
    (x : Γ(tensor (tilde M) (tilde N), PrimeSpectrum.basicOpen f)) :
    (basicTensorEquiv R M N g).symm
        ((tensor (tilde M) (tilde N)).presheaf.map i.op x) =
      sectionTensorRes R M N i ((basicTensorEquiv R M N f).symm x) := by
  apply (basicTensorEquiv R M N g).injective
  rw [LinearEquiv.apply_symm_apply, basicTensorEquiv_restriction,
    LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Modules
end
end

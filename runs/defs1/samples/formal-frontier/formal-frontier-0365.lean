public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)

/-- Restriction of sheaf-tensor sections from `⊤` to `D(f)`, made `R`-linear
using the native `R`-action and `map_smul_Spec`. -/
noncomputable def resTop (f : R) :
    Γ(tensor (tilde M) (tilde N), ⊤) →ₗ[R]
      Γ(tensor (tilde M) (tilde N), PrimeSpectrum.basicOpen f) where
  toFun := (tensor (tilde M) (tilde N)).presheaf.map
    (PrimeSpectrum.basicOpen f).leTop.op
  map_add' := map_add _
  map_smul' r t := map_smul_Spec (PrimeSpectrum.basicOpen f).leTop.op r t

end AlgebraicGeometry.Scheme.Modules
end
end

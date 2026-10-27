public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)

/-- Canonical `R`-linear tensor localization in the explicit `Away f`
presentation, built from native `LocalizedModule.mkLinearMap` and
`IsLocalization.moduleTensorEquiv`, independently of the restriction square. -/
@[expose]
noncomputable def awayLocTensor (f : R) :
    TensorProduct R M N →ₗ[R]
      TensorProduct (Localization.Away f)
        (LocalizedModule (.powers f) M) (LocalizedModule (.powers f) N) :=
  ((IsLocalization.moduleTensorEquiv (.powers f) (Localization.Away f)
    (LocalizedModule (.powers f) M) (LocalizedModule (.powers f) N)
      ).symm.restrictScalars R).toLinearMap.comp
    (TensorProduct.map (LocalizedModule.mkLinearMap (.powers f) M)
      (LocalizedModule.mkLinearMap (.powers f) N))

end AlgebraicGeometry.Scheme.Modules
end
end

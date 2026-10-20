@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Quotient-preserving equivalence between integral controlled and native
dominant rational maps over any scheme. -/
noncomputable def integralDenseOpenEquivalenceOver (S : Scheme.{u}) :
    IntegralDenseOpenRationalSchemeOver S ≌ IntegralDominantRationalSchemeOver S where
  functor := IntegralDenseOpenRationalSchemeOver.toNative
  inverse := IntegralDominantRationalSchemeOver.toDenseOpen
  unitIso := IntegralDenseOpenRationalSchemeOver.nativeUnitIso
  counitIso := IntegralDominantRationalSchemeOver.nativeCounitIso
  functor_unitIso_comp X := by
    change IntegralDenseOpenRationalSchemeOver.toNative.map (𝟙 X) ≫
      𝟙 (IntegralDenseOpenRationalSchemeOver.toNative.obj X) = 𝟙 _
    simp

end AlgebraicGeometry
end

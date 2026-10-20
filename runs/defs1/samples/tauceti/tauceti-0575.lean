open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TrivSqZeroExt DualNumber

open scoped ModuleCat.Algebra

public section

namespace TauCeti

universe u

section CommRing

variable (k : Type u) [CommRing k]

/-- `Hom_A(A, S)` is isomorphic to `k` as a `k`-module, by evaluation at `1`. -/
noncomputable def homDualNumberFreeEquiv :
    (dualNumberFree k ⟶ dualNumberResidue k) ≃ₗ[k] k :=
  ModuleCat.homLinearEquiv ≪≫ₗ LinearMap.ringLmapEquivSelf (DualNumber k) k _ ≪≫ₗ
    dualNumberResidueEquiv k

end CommRing
end TauCeti
end

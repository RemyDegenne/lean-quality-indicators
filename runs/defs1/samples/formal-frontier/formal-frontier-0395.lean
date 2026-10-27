public section

set_option warningAsError true

open CategoryTheory Opposite TopologicalSpace

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}}

namespace IdealSheafData

set_option backward.isDefEq.respectTransparency false in
/-- On an affine open, sections of the ideal sheaf module are the specified ideal. -/
@[expose]
noncomputable def affineSectionsEquiv (I : X.IdealSheafData) (U : X.affineOpens) :
    Γ(I.toModule, U.1) ≃ₗ[Γ(X, U.1)] I.ideal U where
  toFun s := ⟨s.1, by
    rw [← I.ker_subschemeι_app U]
    exact s.2⟩
  invFun s := ⟨s.1, by
    change (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom).val.app (op U.1) s.1 = 0
    change I.subschemeι.app U s.1 = 0
    rw [← RingHom.mem_ker, I.ker_subschemeι_app U]
    exact s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end IdealSheafData
end AlgebraicGeometry.Scheme
end

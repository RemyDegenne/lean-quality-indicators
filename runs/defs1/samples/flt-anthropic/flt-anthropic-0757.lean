namespace P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

noncomputable section

namespace ConstPullback

open Opposite

variable {X : Scheme.{0}}

def homothety (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun s => (res r U) • s
          map_add' := fun a b => smul_add _ a b
          map_smul' := fun a s => by
            change res r U • (a • s) = a • (res r U • s)
            rw [smul_smul, smul_smul, res_comm] }
     naturality := fun {U V} i => by
        ext s
        change res r V • (M.val.map i s) = M.val.map i (res r U • s)
        rw [PresheafOfModules.map_smul, res_map] }⟩

end ConstPullback
end
end P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback

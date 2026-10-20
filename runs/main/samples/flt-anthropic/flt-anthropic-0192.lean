namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage

set_option autoImplicit false

universe u

p2m_open

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_open

namespace AlgebraicGeometry

namespace OModulePresheaf

namespace Rebase

p2m_open

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P) (W : P.affineOpens)

scoped instance isProper_qW [IsProper p] : IsProper (qW p W) := by
  unfold qW; infer_instance

section Bridge0

variable [IsSeparated q] (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover)

theorem e0_smulB (b : Bch W) (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' (b • x) i =
      (p.appLE (W : P.Opens) ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right).hom b • e0 q p W G K' x i := by
  rw [e0_apply, e0_apply, Pi.smul_apply, GW_smul_def]
  erw [G.res_smul]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end Bridge0
end Rebase
end OModulePresheaf
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage

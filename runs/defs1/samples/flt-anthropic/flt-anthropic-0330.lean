namespace P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_twoSidedBlocks_of_isInvertible

set_option autoImplicit false

universe u

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

section S0sec

open TensorProduct

p2m_reactivate

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso Spec.map_preimage Scheme.Hom.fiberι_fiberHomeo_symm Scheme.IdealSheafData.ideal_mul Scheme.IdealSheafData.support_comap pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom Scheme.range_fromSpecResidueField Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme pullbackSpecIso Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Spec.map_injective IsClosedImmersion IsSeparated Spec.preimage Scheme.Modules.pullbackCongr Etale Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelEffCartierDiv mapOnProdOver Scheme.TwoAffineOpenCover graphOver graphOver_fst graphOver_snd prodKerGraph prodKerGraph_eq_prod Scheme.IdealSheafData.IsInvertible SmoothProperCurve.specMap SmoothProperCurve.baseChange SmoothProperCurve.sectionBaseChange RelPicard.BaseChange.κ RelPicard.BaseChange.overR RelPicard.BaseChange.toR RelPicard.BaseChange.toR_pullbackAlong_iso RelPicard.BaseChange.restrict RelPicard.BaseChange.restrict_algEquivZeroCut RelPicard.BaseChange.classesEquiv RelPicard.BaseChange.relSubPicPresheafRestrictIso RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso RelPicard.BaseChange.representableByRestrict DescentAction DescentAction.univ DescentAction.map_repActOver_univ DescentAction.ofRepresentableBy DescentAction.act_comp DescentAction.act Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison prodKerGraph_comap_mapOnProdOver Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso" namespace RelPicard p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle SubPicCondition RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut relSubPicPresheaf relSubPicPresheaf_map_coe sectionIdeal sectionTwist fibreModule BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.rigSection_fst' BaseChange.rigSection_snd' BaseChange.overR BaseChange.toR BaseChange.toR_pullbackAlong_iso BaseChange.restrict BaseChange.restrict_algEquivZeroCut BaseChange.classesEquiv BaseChange.relSubPicPresheafRestrictIso BaseChange.relSubPicPresheafAlgEquivZeroCutIso BaseChange.representableByRestrict sectionFibrePoint" end AlgebraicGeometry.RelPicard

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.RelPicard" in

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

section K1

open AlgebraicGeometry.RelPicard.G2

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
  (R' : Type u) [CommRing R'] [Algebra R R']
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  (t' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R')) (ht' : t' ≫ specMap R R' = specMap R Ω)

p2m_reactivate

section D

open AlgebraicGeometry.RelPicard.G2

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace AlgebraicGeometry

namespace RelPicard

namespace G2

p2m_open

section FibreIso

variable {R' : Type u} [CommRing R'] {C'' : Scheme.{u}} (c'' : C'' ⟶ Spec (CommRingCat.of R'))
  {P : Scheme.{u}} (t₀ : P ⟶ Spec (CommRingCat.of R'))
  {Ω : Type u} [Field Ω] (y : Spec (CommRingCat.of Ω) ⟶ P) (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R'))
  (hx : y ≫ t₀ = x)

def fibreModuleIso (M : (pullback c'' t₀).Modules) :
    fibreModule c'' t₀ y M ≅ (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).obj M) :=
  (Scheme.Modules.pullbackCongr (fibreIso_hom_baseChangeSnd c'' t₀ y x hx).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso c'' t₀ y x hx).hom
      (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).app M).symm

end FibreIso
end G2
end RelPicard
end AlgebraicGeometry
end D
end K1
end AlgebraicGeometry
end S0sec
end
end P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_twoSidedBlocks_of_isInvertible

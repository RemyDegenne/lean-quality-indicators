namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel

attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RelRepGlue

universe u

variable {N : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {n : ℕ} {M : Scheme.{0}} {fM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM}
  (C : Type) [CommRing C] [Algebra 𝒪 C]

scoped instance chartι_isOpenImmersion (U : (MC fM C).affineOpens) : IsOpenImmersion (chartι C U) := by
  unfold chartι; infer_instance

attribute [scoped instance] algebraC algebraO

scoped instance isScalarTower_ringOf (U : (MC fM C).affineOpens) : IsScalarTower 𝒪 C (ringOf (fM := fM) C U) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

section KeyGeneric

variable {S : Type} [CommRing S] (t₁ : Spec (CommRingCat.of S) ⟶ MC fM C)

variable (D : ChartData fM C) {ZS : Scheme.{0}} (ζS : ZS ⟶ Spec (CommRingCat.of S))

variable {D ζS} (L : LocalComparison C t₁ D ζS)

namespace LocalComparison

section Cartesian

variable {T : Scheme.{0}} (a : T ⟶ Spec (CommRingCat.of S)) (b : T ⟶ R C D) (hab : b ≫ qR C D = a ≫ t₁)

noncomputable def ellT (p : SecIdx C t₁) : pullback a ((secCover C t₁).f p) ⟶ D.Z p.1.2 :=
  (ιR_isPullback C D p.1.2).lift
    (pullback.snd a ((secCover C t₁).f p) ≫ (isoW C t₁ p).hom ≫ Spec.map (CommRingCat.ofHom (φW C t₁ p)))
    (pullback.fst a ((secCover C t₁).f p) ≫ b)
    (by rw [Category.assoc, Category.assoc, spec_φW_chartι, isoW_hom_Wι_assoc, ← pullback.condition_assoc,
      Category.assoc, hab])

end Cartesian
end LocalComparison
end KeyGeneric
end RelRepGlue
end
end P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel

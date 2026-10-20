namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_of_descent_of_faithfullyFlat

attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ

attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule

set_option autoImplicit false

p2m_open

open scoped TensorProduct

namespace AlgebraicGeometry

namespace StructureDescentAux

p2m_open

universe u

variable {S : Type u} [CommRing S] {S' : Type u} [CommRing S'] [Algebra S S']

variable {X A' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}

lemma nsmul_comp (c : A' ⟶ X) (hc : CategoryTheory.IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hcmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ c =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
          ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (x : SchemeHomOver t' f') :
    (L'.nsmul t' n x).1 ≫ c =
      (L.nsmul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) n
        ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩).1 := by
  induction n with
  | zero => exact one_comp c hc L L' hcmul t'
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hcmul]
    congr 1
    apply congrArg (fun z => L.mul _ z _)
    exact Subtype.ext ih

end StructureDescentAux
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_of_descent_of_faithfullyFlat

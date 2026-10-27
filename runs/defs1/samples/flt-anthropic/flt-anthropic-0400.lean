namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper

attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero

attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule

set_option autoImplicit false

set_option linter.unusedSectionVars false

universe u

p2m_open

noncomputable section

namespace FormalGAGAFiniteSqZeroAux

p2m_open

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (.of A)} (F : OModulePresheaf q)

scoped instance instModuleMop (U : P.Opens) : Module (Γ(P, U))ᵐᵒᵖ (F.obj U) :=
  Module.compHom (F.obj U) ((RingHom.id Γ(P, U)).fromOpposite fun a b => mul_comm a b)

scoped instance instIsCentralScalar (U : P.Opens) : IsCentralScalar Γ(P, U) (F.obj U) := ⟨fun _ _ => rfl⟩

def α : (toOpensFunctor P).op ⋙ P.presheaf ⟶ Tfun F where
  app U := (CommRingCat.ofHom (algebraMap Γ(P, U.unop.1) (T F U.unop.1)) :
    P.presheaf.obj (op U.unop.1) ⟶ CommRingCat.of (T F U.unop.1))
  naturality {U V} i := by
    ext a
    change algebraMap Γ(P, V.unop.1) (T F V.unop.1) (rmap (toOpens_mono i.unop.le) a) =
      ρ F (toOpens_mono i.unop.le) (algebraMap Γ(P, U.unop.1) (T F U.unop.1) a)
    rw [algebraMap_eq_inl, algebraMap_eq_inl, ρ_inl]

end FormalGAGAFiniteSqZeroAux
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper

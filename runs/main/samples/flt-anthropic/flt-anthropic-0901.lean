namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper

attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule

set_option autoImplicit false

set_option linter.unusedSectionVars false

universe u

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

section Datum

variable (G : OModulePresheaf (p ≫ q))

attribute [local instance] modSec

attribute [local instance] modB

attribute [local instance] modA

theorem algebraMap_smul_GW (O : ((pW p W) : Scheme.{u}).Opens) (a : A) (x : (GW q p W G).obj O) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
     algebraMap A (Bch W) a • x) = a • x := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) ((pW p W).ι ''ᵁ O)
  rw [GW_smul_def, appLE_algebraMap_chart]
  exact algebraMap_smul Γ(V', (pW p W).ι ''ᵁ O) a (show G.obj ((pW p W).ι ''ᵁ O) from x)

end Datum
end Rebase
end OModulePresheaf
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper

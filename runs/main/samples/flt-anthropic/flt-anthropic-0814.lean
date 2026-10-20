namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES

attribute [-instance] ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

noncomputable section

universe u

p2m_open

namespace AlgebraicGeometry

namespace OModulePresheaf

p2m_open

open CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsProper πZ] [IsIntegral Z] (D : ChowDatumProj πZ) :
    ∃ (Q : OModulePresheaf πZ) (S : OModulePresheaf.SES (OModulePresheaf.unit πZ)
          (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) 0) Q),
      Q.IsCoherent ∧ Q.IsQuasicoherent ∧ Q.SupportedIn ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ :=
  AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES' πZ D

end OModulePresheaf
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES

namespace P2MW.S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

universe u

p2m_open

namespace RigCocycle

p2m_open

section general

variable {X B : Scheme.{u}} (rig : B ⟶ X) (𝓠 : X.Modules)
  (α₀ : (Scheme.Modules.pullback rig).obj 𝓠 ≅ SheafOfModules.unit B.ringCatSheaf)

def Normalised (σ : X ⟶ X) (u : B ⟶ B) (h : rig ≫ σ = u ≫ rig)
    (ψ : 𝓠 ≅ (Scheme.Modules.pullback σ).obj 𝓠) : Prop :=
  (Scheme.Modules.pullback rig).mapIso ψ ≪≫ τ rig 𝓠 α₀ σ u h = α₀

end general
end RigCocycle
end P2MW.S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso

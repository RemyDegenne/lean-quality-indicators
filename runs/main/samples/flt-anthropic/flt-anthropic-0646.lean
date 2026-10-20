namespace P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace SepDescAux

section charts

variable {U U' X S : Scheme.{u}} (a : U ⟶ X) (b : U' ⟶ X) (f : X ⟶ S)

lemma chartBC_fst {Y : Scheme.{u}} (g : Y ⟶ S) :
    chartBC a b f g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ chart a b f := by simp [chartBC]

end charts
end SepDescAux
end P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd

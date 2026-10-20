namespace P2MW.S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso

attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe u

p2m_open

p2m_reactivate

p2m_reactivate

namespace Ws31ThetaF

namespace BaseCase

p2m_open

open AlgebraicGeometry.Scheme.Modules

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (N : Z.Modules) (U : Z.Opens) :
    Subsingleton Γ(N, U) := by
  have hU : U = ⊥ := le_bot_iff.mp fun x _ => isEmptyElim x
  let D : TopCat.Sheaf Ab Z.toTopCat := ⟨N.presheaf, N.isSheaf⟩
  have hT : IsTerminal (D.obj.obj (op U)) := D.isTerminalOfEqEmpty hU
  exact AddCommGrpCat.subsingleton_of_isZero hT.isZero

end BaseCase
end Ws31ThetaF
end P2MW.S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso

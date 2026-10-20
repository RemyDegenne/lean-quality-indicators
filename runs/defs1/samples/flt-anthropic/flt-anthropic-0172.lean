namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

universe u

p2m_open

namespace PhiMain

p2m_open

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}

section Test

variable (L : RelativeGroupLaw S f) {R : Type} [CommRing R] {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}

variable (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
  (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))

include L hc hA N T κ

noncomputable def unitVal (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) : Tˣ := by
  classical
  exact if h : KER2 L ι N then (isUnit_rawVal L hc hA N T κ h x hx).unit else 1

end Test
end PhiMain
end P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial

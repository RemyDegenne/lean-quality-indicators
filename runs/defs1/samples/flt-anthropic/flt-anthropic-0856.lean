namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector

attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

namespace F1Asm

set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime]

noncomputable def awayToOne {B : Type} [CommRing B] (f : B) (hf : IsUnit f) :
    Rigidified.Baway f →+* Rigidified.Baway (1 : B) :=
  IsLocalization.Away.lift f (g := Rigidified.awayHom (1 : B)) (hf.map (Rigidified.awayHom (1 : B)))

end F1Asm
end P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector

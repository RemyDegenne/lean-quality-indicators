namespace P2MW.S_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt

attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

universe u

open MvPowerSeries

noncomputable section

namespace B23K5

open MvFormalGroup MvFormalGroup.CartierModule MvFormalGroup.WittLaw B23K4

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}

section Seq

variable [Algebra ℤ_[p] R] (Φ : MvFormalGroup d R) [Φ.IsComm] (f : CartierModule p Φ)

def toCM (G : Fin d → MvPowerSeries ℕ R) (hG : IsLamHom Φ G) : CartierModule p Φ where
  toPowerSeries := fun j => subst (ahFam p R) (G j)
  constantCoeff_eq_zero := (precomp_hom (Φ := Φ) (WittLaw.hasSubst_addFam p R) (BigWittLaw.hasSubst_addFam R)
    hasSubst_ahFam constantCoeff_ahFam
    (fun m => MvFormalGroup.ArtinHasse.subst_addFam_map_coord p R m) hG.1 hG.2).1
  subst_eq := (precomp_hom (Φ := Φ) (WittLaw.hasSubst_addFam p R) (BigWittLaw.hasSubst_addFam R)
    hasSubst_ahFam constantCoeff_ahFam
    (fun m => MvFormalGroup.ArtinHasse.subst_addFam_map_coord p R m) hG.1 hG.2).2

end Seq
end B23K5
end
end P2MW.S_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt

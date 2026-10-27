namespace P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul

set_option autoImplicit false

universe u v

noncomputable section

namespace P2mLawPresW

set_option linter.unusedSectionVars false

open MvPowerSeries

section SeriesPoint

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] {d d' : ℕ} {Φ : MvFormalGroup d R}
  {Φ' : MvFormalGroup d' R} {τ : Type*}

def PInI (n : ℕ) (a : SeriesPoint Φ τ) : Prop := ∀ j, a.val j ∈ ordIdeal τ R n

end SeriesPoint
end P2mLawPresW
end
end P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul

namespace P2MW.S_MvFormalGroup_BigWittLaw_subst_elim_negSeries_hom_and_coeff_eq_zero

set_option autoImplicit false

universe u v

noncomputable section

open MvPowerSeries

namespace P2mK1c

section SeriesPoint

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}
  {τ : Type*}

omit hp in
theorem PInI.sub [Φ.IsComm] {n : ℕ} {a b : SeriesPoint Φ τ} (ha : PInI n a) (hb : PInI n b) :
    PInI n (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

end SeriesPoint
end P2mK1c
end
end P2MW.S_MvFormalGroup_BigWittLaw_subst_elim_negSeries_hom_and_coeff_eq_zero

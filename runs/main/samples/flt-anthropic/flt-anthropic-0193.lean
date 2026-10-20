namespace P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul

set_option autoImplicit false

universe u v

noncomputable section

namespace P2mLawPresW

set_option linter.unusedSectionVars false

open MvPowerSeries

section Section

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]

theorem val_evalPt_cwPt (g : CartierModule p Φ) (i : Fin d) :
    (evalPt g (cwPt p R d i)).val = fun j => subst (fun _ : Unit => (X i : MvPowerSeries (Fin d) R))
      (curve g j) := by
  rw [cwPt, ← substPt_evalPt]
  rfl

end Section
end P2mLawPresW
end
end P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul

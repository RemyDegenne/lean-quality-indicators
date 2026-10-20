namespace P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ

universe u

set_option autoImplicit false

set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

namespace MK00Port

section TorFV

variable {R : Type u} [CommRing R]

theorem torFV_tor_succ_isZero_of_isZero (X : ModuleCat.{u} R) (hX : IsZero X)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj X).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  refine IsZero.of_iso ?_ (torLES_torIso P X (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.ExactAt.of_isZero
    ((tensorRight (P.complex.X (n + 1))).map_isZero hX)

end TorFV
end MK00Port
end
end P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ

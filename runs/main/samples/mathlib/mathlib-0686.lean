public section

variable {R S : Type*} [CommRing R] [CommRing S]

open Function Localization Polynomial TensorProduct PrimeSpectrum Topology

open scoped Pointwise

namespace PrimeSpectrum

lemma isConstructible_comap_C
    {s : Set (PrimeSpectrum (Polynomial R))} (hs : IsConstructible s) :
    IsConstructible (comap Polynomial.C '' s) := by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨T, hT, -⟩ := ChevalleyThm.chevalley_polynomialC _ Submodule.mem_top S (by simp)
  rw [hT]
  exact T.isConstructible_toSet

end PrimeSpectrum
end

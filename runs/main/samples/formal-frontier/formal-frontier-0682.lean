@[expose] public section

universe u

namespace PrimeSpectrum

theorem isClopen_basicOpen_of_krullDimLE_zero {R : Type u} [CommSemiring R]
    [Ring.KrullDimLE 0 R] (a : R) :
    IsClopen (basicOpen a : Set (PrimeSpectrum R)) := by
  haveI : T1Space (PrimeSpectrum R) := ⟨fun x ↦
    (isClosed_singleton_iff_isMaximal x).mpr (Ideal.isMaximal_of_isPrime x.asIdeal)⟩
  refine ⟨?_, isOpen_basicOpen⟩
  rw [← localization_away_comap_range (Localization (Submonoid.powers a)) a]
  refine isClosed_range_of_stableUnderSpecialization _ ?_
  intro x y hxy hx
  exact hxy.eq ▸ hx

end PrimeSpectrum
end

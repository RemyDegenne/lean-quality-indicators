@[expose] public section

open scoped InnerProductSpace

open Filter Topology

namespace TauCeti

namespace DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The restriction of a self-adjoint operator to one of its spectral ranges.

Stated over the Davis--Kahan spectral subspace rather than `specRange`, which it
is definitionally; the instances downstream key on this name. -/
noncomputable def selfAdjointSpectralRestriction
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralSubspace A hA B hB →ₗ.[ℂ]
      selfAdjointSpectralSubspace A hA B hB :=
  TauCeti.LinearPMap.specRestrict hA B hB

end DavisKahan
end TauCeti
end

public section

open Function Set

universe u v

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The clopen subset of the prime spectrum underlying a rank fiber. -/
def rankFiberClopen (i : rankFiberIndex R M) :
    TopologicalSpace.Clopens (PrimeSpectrum R) :=
  ⟨i.1, by
    rw [Function.Fiber.eq_fiber_image]
    exact (rankLocallyConstant R M).isLocallyConstant.isClopen_fiber _⟩

end Module
end

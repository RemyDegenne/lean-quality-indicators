public section

open Function Set

universe u

namespace ModuleCat.FiniteProjective

variable {R : Type u} [CommRing R]

theorem rankModuleFinite
    (f : LocallyConstant (PrimeSpectrum R) ℕ) : Module.Finite R (rankModule R f) := by
  let _ (i : Fin (rankBound f)) : Module.Finite R (Ideal.span {rankIdempotent f i}) :=
    Module.Finite.span_singleton R _
  exact Module.Finite.equiv
    (DirectSum.linearEquivFunOnFintype R (Fin (rankBound f))
      fun i ↦ Ideal.span {rankIdempotent f i})

end ModuleCat.FiniteProjective
end

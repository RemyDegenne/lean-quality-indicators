public section

namespace TauCeti

open Metric Set

namespace PoincareDisc

variable {F : PoincareDisc → PoincareDisc} {f : ℂ → ℂ}

theorem exists_eq_unitDiscStandardAutomorphismIsometryEquiv_of_dist_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hrep : ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ))
    {z w : PoincareDisc} (hne : z ≠ w) (heq : dist (F z) (F w) = dist z w) :
    ∃ (u : Circle) (a : Complex.UnitDisc),
      ∀ ζ : PoincareDisc, F ζ = unitDiscStandardAutomorphismIsometryEquiv u a ζ := by
  have hne' : (toUnitDisc z : ℂ) ≠ (toUnitDisc w : ℂ) := fun h =>
    hne (toUnitDisc.injective (Complex.UnitDisc.coe_injective h))
  have heq' : hyperbolicDist (f (toUnitDisc z : ℂ)) (f (toUnitDisc w : ℂ))
      = hyperbolicDist (toUnitDisc z : ℂ) (toUnitDisc w : ℂ) := by
    simpa only [dist_eq, hrep] using heq
  obtain ⟨u, a, hua⟩ :=
    exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_hyperbolicDist_map_eq hf
      (mapsTo_of_rep hrep) (coe_mem_ball z) (coe_mem_ball w) hne' heq'
  refine ⟨u, a, fun ζ => toUnitDisc.injective (Complex.UnitDisc.coe_injective ?_)⟩
  rw [unitDiscStandardAutomorphismIsometryEquiv_apply, toUnitDisc_toPoincare, hrep ζ]
  exact hua (toUnitDisc ζ)

end PoincareDisc
end TauCeti
end

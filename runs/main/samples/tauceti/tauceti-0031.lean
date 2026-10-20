public section

open Multiplicative Topology

namespace TauCeti.Toric

open AffineSemigroupComplexPoint

variable {N V ι : Type*} [AddCommGroup N]
  [AddCommGroup V] [Module ℝ V] {i : N →+ V} {σ : PointedCone ℝ V} {s : ℕ}

variable (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
  {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N} (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))

include hσ hb in
theorem coneChartEquiv_smul_fst (T : ComplexTorus N)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ) :
    (coneChartEquiv hi hσ hb (T • x)).1 ρ =
      T (b.coord (Sum.inl ρ)).toAddMonoidHom * (coneChartEquiv hi hσ hb x).1 ρ := by
  simp

end TauCeti.Toric
end

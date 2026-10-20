public section

noncomputable section

open LaurentPolynomial Submodule

namespace TauCeti.OrientedPDCode

variable {n : ℕ} (D : OrientedPDCode n)

variable (g₀ : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount)

theorem span_range_reducedAlexanderGenerator :
    span ℤ[T;T⁻¹] (Set.range (D.reducedAlexanderGenerator g₀)) = ⊤ := by
  have hgen : D.reducedAlexanderGenerator g₀ =
      D.alexanderReduction g₀ ∘ D.alexanderGenerator := rfl
  rw [hgen, Set.range_comp, ← Submodule.map_span,
    D.span_range_alexanderGenerator, Submodule.map_top,
    LinearMap.range_eq_top.mpr (D.alexanderReduction_surjective g₀)]

end TauCeti.OrientedPDCode
end
end

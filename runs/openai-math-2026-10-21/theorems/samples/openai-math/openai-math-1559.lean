namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped ENNReal

namespace Invariant233.ProductModel

theorem scalarMultiplier_mem_commutant (θ : ℕ → ℝ) (g : Lp ℂ ∞ baseMeasure) :
    L2Multiplication.multiplier (E := Fiber) g ∈ (factor θ).commutant := by
  apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
  intro A hA
  have hcomm : ∀ a : Lp ℂ ∞ baseMeasure,
      Commute A (L2Multiplication.multiplier (E := Fiber) a) := by
    rcases hA with hA | hA
    · rcases Set.mem_singleton_iff.mp hA with rfl
      exact shiftOperator_commutes_multiplier
    · obtain ⟨f, C, hC, hf, hb, rfl⟩ := hA
      exact multiplier_commutes_scalar θ f C hC hf hb
  exact ⟨(hcomm g).eq, (L2Multiplication.star_commutes_multiplier A hcomm g).eq⟩

end Invariant233.ProductModel
end
end OAI

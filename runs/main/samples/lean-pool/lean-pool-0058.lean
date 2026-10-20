@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization

open AVenhance.Infra.Torus

namespace AVenhance.Infra.Heat

theorem WeakFourier.heatWeak_realCharacter_contDiff (k : Frequency) :
    ContDiff ℝ (⊤ : ℕ∞) (WeakFourier.heatWeakRealCharacter k) := by
  change ContDiff ℝ (⊤ : ℕ∞) (Complex.reCLM ∘ torusCharacter k)
  have hRe : ContDiff ℝ (⊤ : ℕ∞) Complex.reCLM :=
    Complex.reCLM.contDiff.of_le le_top
  have hChar : ContDiff ℝ (⊤ : ℕ∞) (torusCharacter k) :=
    (torusCharacter_contDiff k).of_le le_top
  exact hRe.comp hChar

end AVenhance.Infra.Heat
end
end

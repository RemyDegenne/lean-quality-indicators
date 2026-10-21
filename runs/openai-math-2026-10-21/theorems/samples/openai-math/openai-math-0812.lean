namespace OAI

open Set Metric MeasureTheory

open scoped BigOperators NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem poissonSpan_constant_laplacian {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (f : Fin 2 → SobolevSpace μ hQ) (c : ℝ)
    (hu : ∀ i, IsSobolevHarmonicOn μ hQ Ω (u i))
    (hf : ∀ i, IsConstantLaplacianOn μ hQ Ω (f i) c) (v : Euclidean (n + 2)) :
    IsConstantLaplacianOn μ hQ Ω (sobolevColumnMap μ hQ (poissonSpan μ hQ u f) v)
      (poissonSpanLaplacian n c v) := by
  have hc : ∀ i : Fin (n + 2), IsConstantLaplacianOn μ hQ Ω
      (poissonSpan μ hQ u f i)
      (Fin.append (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin 2 => c) i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [poissonSpan, Fin.append_left] using
        (isConstantLaplacianOn_zero_iff μ hQ Ω (u j)).mpr (hu j)
    · intro j
      simpa only [poissonSpan, Fin.append_right] using hf j
  convert IsConstantLaplacianOn.linearCombination μ hQ hc v using 1
  simp only [poissonSpanLaplacian, LinearMap.sum_apply, LinearMap.smul_apply,
    EuclideanSpace.projₗ, PiLp.projₗ_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end RegularPointCoordinates
end
end OAI

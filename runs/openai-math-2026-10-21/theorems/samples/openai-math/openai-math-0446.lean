namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

open scoped BigOperators

namespace InvariantIsing

theorem priorFiniteGG_individualDiagonal_bound {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (β e C : ℝ) (hC : 0 ≤ C) (ha : 0 < |amplitude j|)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hDb : ∀ U σ, |D U σ| ≤ C)
    (center δ : Fin m → ℝ)
    (hδ : ∀ a, priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) ≤ δ a)
    (hE :
      let A := spectralPerturbationCoefficients (fun ω : PriorFrozenData N j => ω.1)
        I (degree j) n (r j)
      let ν := priorFrozenReference ν₀ eig c I degree amplitude r h j
      let E := fun p : PriorFrozenData N j × (ℕ → ℝ) => ∫ x,
        |cylinderField (A p.1 x) p.2 - β|
        ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
      Integrable E ((priorFrozenLaw μ j).prod gaussianCoordinates) ∧
        (∫ p, E p ∂(priorFrozenLaw μ j).prod gaussianCoordinates) ≤ e) :
    |priorSpectralGGResidual μ ν₀ eig c I degree amplitude r h j D| ≤
      2 * C * (e / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a) := by
  let d₀ := (∏ a, spectralDiagonalCenter (center a) ^ degree j a) *
    ((n : ℝ) / (n + 1 : ℕ)) ^ r j
  have hg := priorFiniteGG_bound μ ν₀ eig c I degree amplitude r h hh h0 j β d₀ e C hC D hD hDb hE
  have hd := priorKernelDiagonalError_le μ ν₀ eig c I degree amplitude r h (degree j) (r j) center
  have hs : (∑ a, (degree j a : ℝ) * priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|)) ≤
      ∑ a, (degree j a : ℝ) * δ a :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hδ a) (Nat.cast_nonneg _)
  have hb := hg.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hd.trans hs) ha.le))
    (mul_nonneg (by norm_num) hC))
  apply (mul_le_mul_iff_left₀ ha).mp
  calc
    _ ≤ 2 * C * (e + |amplitude j| * ∑ a, (degree j a : ℝ) * δ a) := by
      simpa only [mul_comm] using hb
    _ = (2 * C * (e / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a)) * |amplitude j| := by
      field_simp [ha.ne']

end InvariantIsing
end
end OAI

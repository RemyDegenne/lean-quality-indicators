@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic

open CKN.Foundation.Parabolic.Morrey

lemma heatPotential_series_representation_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z q : ParabolicPoint} {r P θ₀ θ₁ : ℝ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i))
    (hδ₀ : 0 < 2 - 5 / θ₀) (hδ₁ : 0 < 1 - 5 / θ₁)
    (hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    heatPotential F G q =
        heatPotentialShellValue F G (heatPotentialNearSet z r) q +
          ∑' j : ℕ, heatPotentialShellValue F G
            (heatPotentialFarShellSet z r j) q ∧
      Summable (fun j : ℕ => heatPotentialShellValue F G
        (heatPotentialFarShellSet z r j) q) := by
  have hcover := heatPotential_near_far_cover (z := z) hr
  have hdST : ∀ j : ℕ, Disjoint (heatPotentialNearSet z r)
      (heatPotentialFarShellSet z r j) := heatPotential_near_far_disjoint hr
  have hdT := heatPotential_far_shells_pairwise_disjoint (z := z) hr
  have hInt := heatPotential_kernel_integrable_on_split hr hP hPθ₀ hPθ₁
    hF hG hNF hNG hSupportF hSupportG hδ₀ hδ₁ hq
  have hFsplit := heatPotential_integral_near_far_split hcover hdST hdT hInt.1
  have hGsplit : ∀ i : Fin 3,
      ∫ v, heatPotentialSpatialKernel i q v * G i v =
        (∫ v in heatPotentialNearSet z r,
          heatPotentialSpatialKernel i q v * G i v) +
          ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i q v * G i v := by
    intro i
    exact heatPotential_integral_near_far_split hcover hdST hdT (hInt.2 i)
  have hsumF : HasSum (fun j : ℕ =>
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialKernel q v * F v)
      (∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
        heatPotentialKernel q v * F v) := by
    apply MeasureTheory.hasSum_integral_iUnion
      (fun j => measurableSet_heatPotentialFarShellSet z r j) hdT
    exact (hInt.1).mono_set subset_union_right
  have hsumG : ∀ i : Fin 3, HasSum (fun j : ℕ =>
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i q v * G i v)
      (∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i q v * G i v) := by
    intro i
    apply MeasureTheory.hasSum_integral_iUnion
      (fun j => measurableSet_heatPotentialFarShellSet z r j) hdT
    exact (hInt.2 i).mono_set subset_union_right
  let g : Fin 3 → ℕ → ℝ := fun i j =>
    ∫ v in heatPotentialFarShellSet z r j,
      heatPotentialSpatialKernel i q v * G i v
  let gU : Fin 3 → ℝ := fun i =>
    ∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
      heatPotentialSpatialKernel i q v * G i v
  have hsumG' : ∀ i : Fin 3, HasSum (g i)
      (gU i) := by
    intro i
    simpa [g, gU] using hsumG i
  have hsumGfin : HasSum (fun j : ℕ => ∑ i : Fin 3, g i j)
      (∑ i : Fin 3, gU i) := by
    classical
    have hsumFin : ∀ s : Finset (Fin 3), HasSum (fun j : ℕ =>
        Finset.sum s (fun i => g i j))
        (Finset.sum s gU) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          have hadd := (hsumG' i).add ih
          simpa [Finset.sum_insert hi, add_comm, add_left_comm, add_assoc] using hadd
    simpa using hsumFin Finset.univ
  have hsumShell : HasSum (fun j : ℕ =>
      heatPotentialShellValue F G (heatPotentialFarShellSet z r j) q)
      ((∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
          heatPotentialKernel q v * F v) +
        ∑ i : Fin 3, ∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
          heatPotentialSpatialKernel i q v * G i v) := by
    have hadd := hsumF.add hsumGfin
    simpa only [heatPotentialShellValue, g, gU] using hadd
  have hcomm : (∑' j : ℕ, ∑ i : Fin 3, g i j) =
      ∑ i : Fin 3, ∑' j : ℕ, g i j := by
    rw [hsumGfin.tsum_eq]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hsumG' i).tsum_eq.symm
  constructor
  · unfold heatPotential
    calc
      (∫ v, heatPotentialKernel q v * F v) +
          ∑ i, ∫ v, heatPotentialSpatialKernel i q v * G i v =
          ((∫ v in heatPotentialNearSet z r,
            heatPotentialKernel q v * F v) +
            ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j,
              heatPotentialKernel q v * F v) +
          ∑ i, ((∫ v in heatPotentialNearSet z r,
            heatPotentialSpatialKernel i q v * G i v) +
            ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j,
              heatPotentialSpatialKernel i q v * G i v) := by
            rw [hFsplit]
            apply congrArg₂ (· + ·) rfl
            apply Finset.sum_congr rfl
            intro i hi
            rw [hGsplit i]
      _ = heatPotentialShellValue F G (heatPotentialNearSet z r) q +
          ((∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
              heatPotentialKernel q v * F v) +
            ∑ i, ∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
              heatPotentialSpatialKernel i q v * G i v) := by
            simp only [heatPotentialShellValue]
            rw [← hsumF.tsum_eq, ← hsumGfin.tsum_eq, hcomm]
            simp_rw [Finset.sum_add_distrib]
            simp only [g]
            ring_nf
      _ = heatPotentialShellValue F G (heatPotentialNearSet z r) q +
          ∑' j : ℕ, heatPotentialShellValue F G
            (heatPotentialFarShellSet z r j) q := by
            rw [← hsumShell.tsum_eq]
  · exact hsumShell.summable

end CKN.Core.HeatPotential
end
end

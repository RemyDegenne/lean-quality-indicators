namespace OAI

section

namespace Erdos3.FixedDensity

namespace GeneratedOrderedPatternRegularization

theorem exists_refinement_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε η : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r)
    (hH : H.EdgeWeightsInUnitInterval)
    {m : ℕ} (hη : 0 ≤ η)
    (hlong : 1 < (m : ℝ) * η ^ 2) :
    ∃ T : GeneratedOrderedPatternRegularization
        G k r H η,
      (∀ e, (T.state e).partition ≤
        (R.state e).partition) ∧
      (∀ e, R.generators e ⊆ T.generators e) ∧
      ∀ e, T.stepIndex e < R.stepIndex e + m := by
  classical
  have he (e : OrderedFace k r) :
      ∃ i : ℕ,
        ∃ S : FaceRegularityState (Fin r → G),
        ∃ F : Finset (BooleanCutTest (Fin r → G)),
          i < m ∧
          S.partition =
            FacePartition.join (R.state e).partition
              (FacePartition.generatedBy F) ∧
          F ⊆ booleanFaceCutSupports G r ∧
          F.card ≤ i ∧
          S.IsFaceCutRegular (H.edgeWeight e) η ∧
          FacePartition.complexity S.partition ≤
            2 ^ i *
              FacePartition.complexity
                (R.state e).partition := by
    exact
      (R.state e).exists_faceCutRegular_refinement_with_generators_before
        hr (H.edgeWeight e)
        (fun y => (hH e y).1)
        (fun y => (hH e y).2)
        hη hlong
  choose i S F hdata using he
  let U :
      (e : OrderedFace k r) →
        Finset (BooleanCutTest (Fin r → G)) :=
    fun e => R.generators e ∪ F e
  have hbudget :
      ∀ e,
        1 <
          ((R.stepIndex e + m : ℕ) : ℝ) * η ^ 2 := by
    intro e
    have hm :
        (m : ℝ) ≤ ((R.stepIndex e + m : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left m (R.stepIndex e)
    exact hlong.trans_le
      (mul_le_mul_of_nonneg_right hm (sq_nonneg η))
  have hstep :
      ∀ e,
        R.stepIndex e + i e <
          R.stepIndex e + m :=
    fun e => Nat.add_lt_add_left (hdata e).1 _
  have hpartition :
      ∀ e, (S e).partition =
        FacePartition.generatedBy (U e) := by
    intro e
    calc
      (S e).partition =
          FacePartition.join (R.state e).partition
            (FacePartition.generatedBy (F e)) :=
        (hdata e).2.1
      _ =
          FacePartition.join
            (FacePartition.generatedBy (R.generators e))
            (FacePartition.generatedBy (F e)) := by
        rw [R.partition_eq_generated e]
      _ = FacePartition.generatedBy (U e) := by
        exact
          (FacePartition.generatedBy_union
            (R.generators e) (F e)).symm
  have hsupported :
      ∀ e, U e ⊆ booleanFaceCutSupports G r := by
    intro e
    exact Finset.union_subset
      (R.generators_supported e)
      (hdata e).2.2.1
  have hcard :
      ∀ e, (U e).card ≤ R.stepIndex e + i e := by
    intro e
    calc
      (U e).card ≤
          (R.generators e).card + (F e).card :=
        by
          change
            (R.generators e ∪ F e).card ≤
              (R.generators e).card + (F e).card
          exact Finset.card_union_le
            (R.generators e) (F e)
      _ ≤ R.stepIndex e + i e :=
        Nat.add_le_add
          (R.generator_card_le e)
          (hdata e).2.2.2.1
  have hregular :
      ∀ e, (S e).IsFaceCutRegular
        (H.edgeWeight e) η :=
    fun e => (hdata e).2.2.2.2.1
  have hcomplexity :
      ∀ e, FacePartition.complexity (S e).partition ≤
        2 ^ (R.stepIndex e + i e) := by
    intro e
    calc
      FacePartition.complexity (S e).partition ≤
          2 ^ i e *
            FacePartition.complexity
              (R.state e).partition :=
        (hdata e).2.2.2.2.2
      _ ≤ 2 ^ i e * 2 ^ R.stepIndex e :=
        Nat.mul_le_mul_left _ (R.complexity_le e)
      _ = 2 ^ (R.stepIndex e + i e) := by
        simp [pow_add, Nat.mul_comm]
  let T : GeneratedOrderedPatternRegularization
      G k r H η := {
    state := S
    generators := U
    budgetLength := fun e => R.stepIndex e + m
    stepIndex := fun e => R.stepIndex e + i e
    budget_large := hbudget
    step_lt_budget := hstep
    partition_eq_generated := hpartition
    generators_supported := hsupported
    generator_card_le := hcard
    regular := hregular
    count_close :=
      patternCount_abs_sub_regularizedOrderedPattern_le
        H hH S hregular
    complexity_le := hcomplexity
  }
  refine ⟨T, ?_, ?_, ?_⟩
  · intro e
    change (S e).partition ≤ (R.state e).partition
    rw [(hdata e).2.1]
    exact FacePartition.join_le_left _ _
  · intro e
    change R.generators e ⊆ U e
    exact Finset.subset_union_left
  · intro e
    change R.stepIndex e + i e <
      R.stepIndex e + m
    exact hstep e

end GeneratedOrderedPatternRegularization
end Erdos3.FixedDensity
end
end OAI

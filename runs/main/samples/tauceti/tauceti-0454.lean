public section

open Filter Function Manifold Set

open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]

attribute [local instance] LieGroup.minSmoothnessThree

theorem exists_eq_mulInvariantOneParameterSubgroup [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G]
    (φ : ContinuousMonoidHom (Multiplicative ℝ) G) :
    ∃ v : GroupLieAlgebra I G, φ = mulInvariantOneParameterSubgroup v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let log : ℕ → E := continuousOneParameterLog (I := I) (G := G) φ
  obtain ⟨X, hlogX⟩ :=
    exists_eventually_continuousOneParameterLog_eq_dyadicStep_smul (I := I) (G := G) φ
  have hφ := tendsto_continuousMonoidHom_dyadicStep φ
  have hexp : ∀ᶠ n in atTop,
      mulInvariantExp (I := I) (G := G) (log n : GroupLieAlgebra I G) =
        φ (Multiplicative.ofAdd (dyadicStep n)) := by
    have h := hφ.eventually
      (eventually_mulInvariantExp_log (I := I) (G := G))
    simpa only [log, continuousOneParameterLog] using h
  let ψ : ContinuousMonoidHom (Multiplicative ℝ) G :=
    mulInvariantOneParameterSubgroup (I := I) (G := G) (X : GroupLieAlgebra I G)
  have hdyadic : ∀ᶠ n in atTop,
      φ (Multiplicative.ofAdd (dyadicStep n)) =
        ψ (Multiplicative.ofAdd (dyadicStep n)) := by
    filter_upwards [hexp, hlogX] with n hexpn hlogn
    have hlogn' : log n = dyadicStep n • X := by
      simpa only [log] using hlogn
    have hsmul : ((dyadicStep n • X : E) : GroupLieAlgebra I G) =
        dyadicStep n • (X : GroupLieAlgebra I G) :=
      (groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).symm.map_smul
        (dyadicStep n) X
    calc
      φ (Multiplicative.ofAdd (dyadicStep n)) =
          mulInvariantExp (I := I) (G := G) (log n : GroupLieAlgebra I G) := hexpn.symm
      _ = mulInvariantExp (I := I) (G := G)
          (dyadicStep n • (X : GroupLieAlgebra I G)) := by
        rw [hlogn', hsmul]
      _ = ψ (Multiplicative.ofAdd (dyadicStep n)) := by
        have hψ := mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul
          (I := I) (G := G) (X : GroupLieAlgebra I G) (dyadicStep n)
        -- Expose the local abbreviation so the public exponential identity applies.
        change ψ (Multiplicative.ofAdd (dyadicStep n)) =
          mulInvariantExp (I := I) (G := G)
            (dyadicStep n • (X : GroupLieAlgebra I G)) at hψ
        exact hψ.symm
  let S : Subgroup (Multiplicative ℝ) := φ.toMonoidHom.eqLocus ψ.toMonoidHom
  have hSdense : Dense (S : Set (Multiplicative ℝ)) := by
    let _ : OrderTopology (Multiplicative ℝ) := inferInstanceAs (OrderTopology ℝ)
    apply S.dense_of_not_isolated_one
    intro ε hε
    have hlt : ∀ᶠ n in atTop, dyadicStep n < ε :=
      (tendsto_order.1 tendsto_dyadicStep).2 ε hε
    obtain ⟨n, hnlt, hneq⟩ := (hlt.and hdyadic).exists
    refine ⟨Multiplicative.ofAdd (dyadicStep n), ?_, ?_, ?_⟩
    · exact hneq
    · exact dyadicStep_pos n
    · exact hnlt
  refine ⟨(X : GroupLieAlgebra I G), ?_⟩
  apply ContinuousMonoidHom.ext
  exact congrFun <| Continuous.ext_on hSdense φ.continuous ψ.continuous fun _ ht => ht

end
end

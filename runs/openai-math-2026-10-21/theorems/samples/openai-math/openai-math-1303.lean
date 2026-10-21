namespace OAI

section

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert

open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ComplexMatrix GeometricChart

open TemperedDistribution EuclideanSobolevOperators HilbertSobolev Set

open scoped Manifold ContDiff SchwartzMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in

lemma hodge_antiRHS_bound (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (U : Set Space) (hχ : ∀ z ∈ U, χ z = 1) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 3,
        (∀ f, toDistribution Space (C 6) 3 (L f) =
          smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
            (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
        ∀ f, ‖L f‖ ≤ B*(r⁻¹)^3*‖f‖)
    (ρ : 𝓢(Space,ℝ)) (hρ : tsupport ρ ⊆ U) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ a : PreL2 A J α hs ht true,
        ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
          (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
            (smoothAntiProjection A J α hs ht a)))‖ ≤
          C₀*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  let ρc := SchwartzMap.postcompCLM Complex.ofRealCLM ρ
  let M := antiPairSelector.comp antiMatrix
  let N : H Space (C 6) 3 →L[ℂ] H Space (C 2) 3 :=
    (2:ℂ) • (product 3 ρc).comp (fiberOperator 3 M)
  refine ⟨‖N‖*B,mul_nonneg (norm_nonneg _) hB,fun r hr hr1 a => ?_⟩
  obtain ⟨L,he,hb⟩ := hL r hr hr1
  let f := smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)
  have hsupp : tsupport ρc ⊆ U :=
    (tsupport_comp_subset (map_zero Complex.ofRealCLM) ρ).trans hρ
  have hdist : toDistribution Space (C 2) 3 (N (L f)) =
      (SchwartzMap.postcompCLM (embed 2)
        (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
          (smoothAntiProjection A J α hs ht a)) : 𝓢'(Space,C 2)) := by
    rw [weightedRawRHS_full_distribution]
    change toDistribution Space (C 2) 3 (N (L f)) =
      (2:ℂ) • smulLeftCLM (C 2) ρc (fiberMap antiPairSelector
        (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeSmooth A J α hs ht (preAntiProjection A J α hs ht a))))
    rw [preAntiProjection_apply,hodgeRawDistribution_smooth_antiInvariant]
    simp only [N,smul_apply,ContinuousLinearMap.comp_apply,map_smul]
    have hp (u : H Space (C 2) 3) : toDistribution Space (C 2) 3 (product 3 ρc u) =
        smulLeftCLM (C 2) ρc (toDistribution Space (C 2) 3 u) := by
      simpa only [Nat.cast_ofNat] using toDistribution_product (F := C 2) 3 ρc u
    have hef := he f
    dsimp only [f] at hef
    rw [hodgeRegularizedGraph_smoothShift_cube] at hef
    rw [hp,toDistribution_fiberOperator,hef,fiberMap_product]
    rw [local_cutoff_one χ ρc (fun z hz => hχ z (hsupp hz))]
    congr 2
  have hn : schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
      (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
        (smoothAntiProjection A J α hs ht a))) = N (L f) := by
    apply toDistribution_injective (3:ℝ)
    rw [schwartzToH_spec,hdist]
  rw [hn]
  calc
    _ ≤ ‖N‖*‖L f‖ := N.le_opNorm _
    _ ≤ ‖N‖*(B*(r⁻¹)^3*‖f‖) := mul_le_mul_of_nonneg_left (hb f) (norm_nonneg _)
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert
end
end
end
end
end OAI

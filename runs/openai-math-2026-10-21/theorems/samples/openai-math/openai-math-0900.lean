namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry

open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

open scoped Classical

theorem source_observable_means (hn : 2 ≤ Fintype.card V) (w w₁ : V → V → ℝ)
    (hw : ∀ x y,0 < w x y) (hz : 0 < partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4 ≤ rowMax hn w x) (hrhi : ∀ x,rowMax hn w x ≤ 1)
    (hlo : ∀ x y,x≠y → (1+1/(Fintype.card V:ℝ))⁻¹*w x y ≤ w₁ x y)
    (hhi : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) :
    let D := sourceD (V:=V) K
    let a := ∑ q : SourceMarked w K,sourceLaw w K D q*observableA w K q
    let d := ∑ q : SourceMarked w K,sourceLaw w K D q*observableD w w₁ K q
    (∑ q : SourceMarked w K,sourceLaw w K D q)=1 ∧
    (∀ q : SourceMarked w K,0 ≤ sourceLaw w K D q) ∧
    (1:ℝ)/2 ≤ a ∧ (1:ℝ)/4 ≤ d ∧
    d/a=partition w₁ ∅/partition w ∅ ∧ (1:ℝ)/2 ≤ d/a ∧ d/a ≤ 1 ∧
    (∀ e : LogicalEdge V,
      (D:ℝ)*(∑ q : SourceMarked w K,sourceLaw w K D q*observableProbe w w₁ K e q)/d=
        Switching.holeRatio w₁ {source e,target e}) := by
  dsimp only
  let D := sourceD (V:=V) K
  have hp := sourceBagZ_pos w hw hz K D
  have hb := sourceBagZ_bounds hn w hw hz hrlo hrhi K hK
  have hc := partition_cooling hn w w₁ (fun x y => (hw x y).le) hlo hhi ∅
  have hz₁ : 0 < partition w₁ ∅ := (half_pos hz).trans_le hc.1
  have hC := sourceC_pos w K
  have hDn : (D:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (sourceD_one (V:=V) K))
  refine ⟨sourceLaw_sum w K D hp.ne',sourceLaw_nonneg w hw K D hp.le,?_,?_,?_,?_,?_,?_⟩
  · rw [observableA_mean w hz]
    apply (le_div_iff₀ hp).mpr
    nlinarith [hb.2]
  · rw [observableD_mean w w₁ hw hz₁]
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc.1 hC.le,hb.2]
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    field_simp [hC.ne',hz.ne',hp.ne']
    simpa only [D] using div_self hp.ne'
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    have he : (sourceC w K*partition w₁ ∅/sourceBagZ w K D)/
        (sourceC w K*partition w ∅/sourceBagZ w K D)=partition w₁ ∅/partition w ∅ := by
      field_simp [hC.ne',hz.ne',hp.ne']
    rw [he]
    exact (le_div_iff₀ hz).mpr (by linarith)
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    have he : (sourceC w K*partition w₁ ∅/sourceBagZ w K D)/
        (sourceC w K*partition w ∅/sourceBagZ w K D)=partition w₁ ∅/partition w ∅ := by
      field_simp [hC.ne',hz.ne',hp.ne']
    rw [he]
    exact (div_le_one hz).mpr hc.2
  · intro e
    rw [observableProbe_mean w w₁ hw,observableD_mean w w₁ hw hz₁]
    unfold Switching.holeRatio
    dsimp only [D] at hDn hp ⊢
    field_simp [hC.ne',hz₁.ne',hp.ne',hDn]

end MatchingFPRAS.Enlargement
end OAI

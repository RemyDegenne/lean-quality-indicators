public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic

open scoped Topology

noncomputable section

namespace ESS

theorem buGaussian_shifted_trace_strip_tendsto
    {B : Set Vec3} {σ : ℝ}
    (hB : MeasurableSet B)
    (u : ParabolicPoint → Vec3)
    (htrace : Tendsto (fun ε : ℝ =>
      (∫ q in B ×ˢ Ioc ε (2 * ε),
        vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ =>
      (∫ z in spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε)),
        vec3EuclideanNorm
          (u ((buGaussianTimeShiftPoint σ).symm z)) ^ 2) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let τprod : (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
    Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.addLeft σ)
  have hτpres : MeasurePreserving τprod
      (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact (MeasurePreserving.id (volume : Measure Vec3)).prod
      (measurePreserving_add_left (volume : Measure ℝ) σ)
  have hτapply (q : Vec3 × ℝ) : τprod q = (q.1, q.2 + σ) := by
    change (q.1, σ + q.2) = (q.1, q.2 + σ)
    congr 1
    ring_nf
  have hτsymm (q : Vec3 × ℝ) : τprod.symm q = (q.1, q.2 - σ) := by
    apply τprod.injective
    rw [τprod.apply_symm_apply, hτapply]
    exact Prod.ext rfl (by ring_nf)
  have himage (ε : ℝ) :
      τprod '' (B ×ˢ Ioc ε (2 * ε)) =
        B ×ˢ Ioc (σ + ε) (σ + 2 * ε) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hτapply]
      exact ⟨hp.1, by constructor <;> linarith only [hp.2.1, hp.2.2]⟩
    · intro hq
      refine ⟨(q.1, q.2 - σ), ?_, ?_⟩
      · refine ⟨hq.1, ?_⟩
        constructor <;> linarith only [hq.2.1, hq.2.2]
      · rw [hτapply]
        exact Prod.ext rfl (by ring_nf)
  have hprodEq (ε : ℝ) :
      (∫ q in B ×ˢ Ioc (σ + ε) (σ + 2 * ε),
        vec3EuclideanNorm
          (u ((buGaussianTimeShiftPoint σ).symm
            (parabolicHomeomorph.symm q))) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q in B ×ˢ Ioc ε (2 * ε),
        vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ)) := by
    let F : Vec3 × ℝ → ℝ := fun q =>
      vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
    have hchange := hτpres.setIntegral_image_emb τprod.measurableEmbedding
      (fun q => F (τprod.symm q)) (B ×ˢ Ioc ε (2 * ε))
    rw [himage ε] at hchange
    have hleft :
        (∫ q in B ×ˢ Ioc (σ + ε) (σ + 2 * ε),
          F (τprod.symm q) ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ q in B ×ˢ Ioc (σ + ε) (σ + 2 * ε),
          vec3EuclideanNorm
            (u ((buGaussianTimeShiftPoint σ).symm
              (parabolicHomeomorph.symm q))) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := by
      apply setIntegral_congr_ae
        (hB.prod measurableSet_Ioc)
      filter_upwards [] with q
      intro hqmem
      rw [hτsymm]
      rw [parabolicHomeomorph_symm_apply]
      change vec3EuclideanNorm (u (q.1, q.2 - σ)) ^ 2 =
        vec3EuclideanNorm
          (u ((buGaussianTimeShiftPoint σ).symm (q.1, q.2))) ^ 2
      have hq := buGaussian_timeShift_point_symm_apply σ
        (show ParabolicPoint from q)
      rw [← hq]
    have hright :
        (∫ q in B ×ˢ Ioc ε (2 * ε),
          F (τprod.symm (τprod q))
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ q in B ×ˢ Ioc ε (2 * ε),
          vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := by
      apply setIntegral_congr_ae
        (hB.prod measurableSet_Ioc)
      filter_upwards [] with q
      simp [F]
    rw [hleft, hright] at hchange
    exact hchange
  have hfun :
      (fun ε : ℝ =>
        (∫ z in spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε)),
          vec3EuclideanNorm (u ((buGaussianTimeShiftPoint σ).symm z)) ^ 2) /
          ε ^ 2) =
      (fun ε : ℝ =>
        (∫ q in B ×ˢ Ioc ε (2 * ε),
          vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2) := by
    funext ε
    rw [setIntegral_parabolic_to_product]
    rw [hprodEq ε]
  rw [hfun]
  exact htrace

end ESS
end
end

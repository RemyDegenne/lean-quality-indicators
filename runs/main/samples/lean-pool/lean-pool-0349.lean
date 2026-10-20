public section

open MeasureTheory Filter Set Metric

open scoped ENNReal Topology Convolution

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

theorem lerayHopfLimit_mollifiedInitial_pairing_tendsto
    (ρ : RegMollifierProfile) {a : Vec3 → Vec3} (ha : MemLp a 2 volume)
    (εs : ℕ → ℝ) (hpos : ∀ n, 0 < εs n) (hlim : Tendsto εs atTop (𝓝 0))
    (w : Vec3 → Vec3) (hw : MemLp w 2 volume) :
    Tendsto (fun n => ∫ x, ∑ i : Fin 3,
        regUniformMollifiedInitial ρ (εs n) (hpos n) a x i * w x i)
      atTop (𝓝 (∫ x, ∑ i : Fin 3, a x i * w x i)) := by
  let f : L2Vec3 → L2Vec3 := regUniformSpatialField a
  have hf : MemLp f 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => a (WithLp.ofLp x)) 2 volume :=
      ha.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hJ : ∀ n, MemLp (regUniformMollifiedInitial ρ (εs n) (hpos n) a) 2 volume := by
    intro n
    refine MemLp.of_eval (fun i => ?_)
    exact (lerayHopfLimit_mollifiedInitial_component_sq_le ρ (εs n) (hpos n) ha i).1
  let E : ∀ g : Vec3 → Vec3, MemLp g 2 volume → Lp L2Vec3 2 (volume : Measure Vec3) :=
    fun g hg => (lerayHopfLimit_toLp_memLp hg).toLp (fun x => WithLp.toLp 2 (g x))
  have hinner : ∀ g (hg : MemLp g 2 volume),
      inner ℝ (E g hg) (E w hw) = ∫ x, ∑ i : Fin 3, g x i * w x i := by
    intro g hg
    simpa using inner_toLp_vec3_eq_integral_dot_measure volume
      (fun x => (WithLp.toLp 2 (g x) : L2Vec3)) (fun x => WithLp.toLp 2 (w x))
      (lerayHopfLimit_toLp_memLp hg) (lerayHopfLimit_toLp_memLp hw)
  have hconv : Tendsto (fun n => E _ (hJ n)) atTop (𝓝 (E a ha)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm : ∀ n, ‖E _ (hJ n) - E a ha‖ =
        (eLpNorm (regMollifyVector ρ (εs n) (hpos n) f - f) 2 volume).toReal := by
      intro n
      change ‖(lerayHopfLimit_toLp_memLp (hJ n)).toLp _ -
        (lerayHopfLimit_toLp_memLp ha).toLp _‖ = _
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
      congr 1
      have hmeas : AEStronglyMeasurable
          (regMollifyVector ρ (εs n) (hpos n) f - f) volume :=
        (regMollifyVector_aestronglyMeasurable ρ (εs n) (hpos n) hf).sub
          hf.aestronglyMeasurable
      exact eLpNorm_comp_measurePreserving hmeas vec3ToL2Vec3_measurePreserving
    simp only [hnorm]
    have h := lerayHopfLimit_regMollifyVector_tendsto ρ hf εs hpos hlim
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h'
    exact h'
  have hlimit := (hconv.inner (𝕜 := ℝ) (tendsto_const_nhds (x := E w hw)))
  rw [hinner a ha] at hlimit
  exact hlimit.congr (fun n => hinner _ (hJ n))

end CKN.Leray
end
end

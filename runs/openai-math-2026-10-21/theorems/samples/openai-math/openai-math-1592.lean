namespace OAI

section

noncomputable section

open MeasureTheory Set Filter Function

open scoped Topology ENNReal NNReal

namespace ThreeTorus

lemma flat_circle_branch {f D : ℝ → ℝ} {l u o : ℝ}
    {ζ : UnitAddCircle → UnitAddCircle}
    (hlu : l ≤ u) (hfm : Measurable f) (hDm : Measurable D)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt f (D x) (Icc l u) x)
    (hmono : StrictMonoOn f (Icc l u)) (hperiod : f u = f l+1)
    (hi : Icc l u ⊆ Ioc o (o+1)) (hζ : Measurable ζ)
    (hζf : ∀ x ∈ Icc l u, ζ (x : UnitAddCircle) = (f x : UnitAddCircle)) :
    (AddCircle.haarAddCircle.withDensity
      (((Icc l u).indicator (fun x => ENNReal.ofReal |D x|)) ∘ circleRep o)).map ζ =
      AddCircle.haarAddCircle := by
  let q : ℝ → ℝ≥0∞ := (Icc l u).indicator (fun x => ENNReal.ofReal |D x|)
  have hq : Measurable q := hDm.abs.ennreal_ofReal.indicator measurableSet_Icc
  have hqs : Function.support q ⊆ Ioc o (o+1) := by
    intro x hx
    apply hi
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  change (AddCircle.haarAddCircle.withDensity (q ∘ circleRep o)).map ζ = _
  rw [← circle_weight_lift hq hqs,
    Measure.map_map hζ AddCircle.measurable_mk']
  calc
    _ = (volume.withDensity q).map (fun x : ℝ => (f x : UnitAddCircle)) := by
      apply Measure.map_congr
      change ∀ᵐ (x : ℝ) ∂volume.withDensity q, ζ (x : UnitAddCircle) = (f x : UnitAddCircle)
      rw [ae_withDensity_iff hq]
      filter_upwards [] with x hx
      exact hζf x (by
        by_contra hn
        exact hx (indicator_of_notMem hn _))
    _ = _ := by
      rw [show volume.withDensity q =
        (volume.restrict (Icc l u)).withDensity (fun x => ENNReal.ofReal |D x|) from
          withDensity_indicator measurableSet_Icc _]
      exact flat_branch_mod_one hlu hfm hD hmono hperiod

end ThreeTorus
end
end
end OAI

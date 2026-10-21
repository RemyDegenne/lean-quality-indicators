namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder

open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma freshPair_second {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d)
    {E : Set (Environment d × Path d)} (hE : MeasurableSet E) :
    freshPair μ x z {ξ | (ξ.1,ξ.2.2) ∈ E} = freshJoint μ z E := by
  change freshPair μ x z ((fun ξ => (ξ.1,ξ.2.2)) ⁻¹' E) = _
  rw [freshPair_apply μ x z (hE.preimage (measurable_fst.prodMk measurable_snd.snd)),
    freshJoint_apply μ z hE]
  apply lintegral_congr
  intro ω
  rw [show (Prod.mk ω ⁻¹' (fun ξ : Environment d × (Path d × Path d) => (ξ.1,ξ.2.2)) ⁻¹' E) =
    Set.univ ×ˢ (Prod.mk ω ⁻¹' E) by ext p; simp]
  rw [Measure.prod_prod,measure_univ,one_mul]

end DirectionalZeroOne
end OAI

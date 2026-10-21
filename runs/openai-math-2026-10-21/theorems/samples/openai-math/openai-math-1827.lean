namespace OAI

namespace RegularPointCoordinates

section

open Set Filter MeasureTheory Metric TopologicalSpace

open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

attribute [local instance] pathBorel pathBorelSpace

lemma transportCost_map_pair {A : Type*} [MeasurableSpace A] [SeparableSpace X]
    (σ : Measure A) (f g : A → X) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (fun z => dist (f z) (g z)^2) σ) :
    transportCost (σ.map (fun z => (f z,g z))) =
      ENNReal.ofReal (∫ z, dist (f z) (g z)^2 ∂σ) := by
  rw [transportCost,lintegral_map
    ((measurable_fst.dist measurable_snd).ennreal_ofReal.pow_const 2) (hf.prodMk hg)]
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro z
  exact (ENNReal.ofReal_pow dist_nonneg 2).symm

end
end RegularPointCoordinates
end OAI

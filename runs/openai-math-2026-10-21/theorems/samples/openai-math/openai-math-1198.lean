namespace OAI

open Set Filter MeasureTheory

open scoped ENNReal NNReal Topology

section InlinedFile16

noncomputable section

namespace WeakHessian

open Set Filter MeasureTheory

open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]

variable {m : Measure X}

lemma weighted_gamma_root_difference_bound (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v φ : X → ℝ}
    (hu : Sobolev m u) (hv : Sobolev m v) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    |(∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m)| ≤
      (L:ℝ)*‖(hu.1.sub hv.1).toLp (fun x => u x-v x)‖*‖hu.2.2.toLp (weakGradient m u)‖+
      (L:ℝ)*‖hv.1.toLp v‖*‖(hu.sub hfin hv).2.2.toLp (weakGradient m (fun x => u x-v x))‖ := by
  let hsub := hu.sub hfin hv
  have h1 := hu.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hu hφ)
  have h2 := hv.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hv hφ)
  have h3 := (hu.1.sub hv.1).integrable_mul (memLp_gamma_lipschitz hfin hpar hu hφ)
  have h4 := hv.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hsub hφ)
  have he : (∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m) =
      (∫ x,(u x-v x)*gamma m u φ x ∂m)+(∫ x,v x*gamma m (fun y => u y-v y) φ x ∂m) := by
    change (∫ x,(u * gamma m u φ) x ∂m)-(∫ x,(v * gamma m v φ) x ∂m) =
      (∫ x,((u-v)*gamma m u φ) x ∂m)+(∫ x,(v*gamma m (fun y => u y-v y) φ) x ∂m)
    rw [← integral_sub h1 h2,← integral_add h3 h4]
    apply integral_congr_ae
    filter_upwards [gamma_sub_left hfin hpar hu.2.1 hv.2.1 (localSobolev_of_lipschitz hfin hφ)] with x hx
    simp only [Pi.mul_apply,Pi.sub_apply]
    rw [hx]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_weighted_gamma_lipschitz_le hfin hpar (hu.1.sub hv.1) hu hφ)
    (abs_weighted_gamma_lipschitz_le hfin hpar hv.1 hsub hφ))

end WeakHessian
end
end InlinedFile16
end OAI

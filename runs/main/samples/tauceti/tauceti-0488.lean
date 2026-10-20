public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace

open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ}

variable [DecidableEq ι]

theorem UniformlyEllipticOn.value_le_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {q : ℝ≥0∞} (hq : 2 < q) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u v : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) ≤
          energyFormH1 a b c v (w : W1p mu Omega 2)) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  have hsub := h.value_le_const_of_forall_eLpNorm_le ha hb hc hb_bound hc_bound hc_nonneg hq hsob
    le_rfl (u := u - v) (by rwa [W1p.posPartAbove_zero]) fun w hw ↦ by
      rw [energyFormH1_sub_left hcoeff]
      exact sub_nonpos.2 (huv w hw)
  have hvalue : W1p.value (u - v) = W1p.value u - W1p.value v := by
    simp only [← W1p.valueL_apply, map_sub]
  filter_upwards [hsub, Lp.coeFn_sub (W1p.value u) (W1p.value v)] with x hx hval
  rw [hvalue, hval, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

end TauCeti.PDE
end
end

@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHierarchy

section

open Filter Topology

open scoped BigOperators Topology

theorem sphericalCodeRate_le_of_eventually_exponential
    {s R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ᶠ n : ℕ in atTop,
      ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) <
        (2 : ℝ) ^ (R * (n : ℝ))) :
    sphericalCodeRate s ≤ R := by
  let w : ℕ → ℝ := fun n =>
    Real.logb 2
      ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) / (n : ℝ)
  have hlower : atTop.IsBoundedUnder (· ≥ ·) w :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (sphericalCodeLogRate_nonneg s))
  have hpoint : ∀ᶠ n : ℕ in atTop, w n ≤ R := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    by_cases hzero : (SpherePacking.sphericalCodeNumber n s).toNat = 0
    · simpa [w, hzero] using hR
    · have hcard :
          0 < ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      have hlog :
          Real.logb 2
            ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) <
              R * (n : ℝ) :=
        (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hcard).2 hn
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
      exact (div_le_iff₀ hnreal).2 hlog.le
  have hconstant : Tendsto (fun _ : ℕ => R) atTop (nhds R) :=
    tendsto_const_nhds
  have hcomparison :
      Filter.limsup w atTop ≤ Filter.limsup (fun _ : ℕ => R) atTop :=
    Filter.limsup_le_limsup hpoint hlower.isCoboundedUnder_le
      hconstant.isBoundedUnder_le
  exact hcomparison.trans_eq hconstant.limsup_eq

end
end HigherHierarchy
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end

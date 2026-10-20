@[expose] public section

open Finset

namespace Zeta5Irrational

lemma V_529 :
    ((4732002263155807105589 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(986142542453729802313 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3889481773370539 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (661117047132910503789 / 2000000000000000000000 : ℝ))) -
              6 * (192233570110948262549 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (38727855271377 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (38727855271377 / 64000000000000 : ℝ)) =
      Real.log (102727855271377 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((38727855271377 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39087855271377 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4732002263155807105589 / 10000000000000000000000 : ℝ) ≤
      Real.log (102727855271377 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39087855271377 / 64000000000000 : ℝ) ≤
      (-(986142542453729802313 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (39087855271377 / 64000000000000 : ℝ) = (39087855271377 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39087855271377 / 32000000000000 : ℝ) ≤
            (400151818146270197687 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3889481773370539 / 5000000000000000 : ℝ) ≤ Real.sqrt (38727855271377 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (38727855271377 / 64000000000000 : ℝ) ≤
      (7778963546741081 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (38727855271377 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau830 :
    Real.arctan (7778963546741081 / 22669343860734325 : ℝ) ≤
      (661117047132910503789 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau829 :
    Real.arctan (7778963546741081 / 10000000000000000 : ℝ) ≤
      (2 * (661117047132910503789 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (506773754429373 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (7778963546741081 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7778963546741081 / 10000000000000000 : ℝ) /
                (1 + (506773754429373 / 400000000000000 : ℝ)) =
              (7778963546741081 / 22669343860734325 : ℝ)
            by
        norm_num];
        exact hau830)
  have hat1 :
    (Real.pi / 2 - (2 * (661117047132910503789 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7778963546741081 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7778963546741081 : ℝ) =
              (7778963546741081 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau829)
  have hz1 :
    (10000000000000000 / 7778963546741081 : ℝ) ≤
      1 / Real.sqrt (38727855271377 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7778963546741081 : ℝ) =
          1 / (7778963546741081 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3889481773370539 : ℝ) ≤
      (192233570110948262549 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (38727855271377 / 64000000000000 : ℝ) ≤
      (375000000000000 / 3889481773370539 : ℝ) := by
    rw [show
        (375000000000000 / 3889481773370539 : ℝ) =
          (3 / 40) / (3889481773370539 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (661117047132910503789 / 2000000000000000000000 : ℝ))) -
        6 * (192233570110948262549 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (38727855271377 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (38727855271377 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3889481773370539 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (661117047132910503789 / 2000000000000000000000 : ℝ))) -
          6 * (192233570110948262549 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (38727855271377 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (38727855271377 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (38727855271377 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
end

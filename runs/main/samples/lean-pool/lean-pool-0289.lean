@[expose] public section

open Finset

namespace Zeta5Irrational

lemma V_242 :
    ((925082402975123894543 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(978797156642601188271 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4508195537539797 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (132354768328260144823 / 312500000000000000000 : ℝ)) -
              6 * (1648538651467957972391 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3251812320751 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3251812320751 / 16000000000000 : ℝ)) =
      Real.log (19251812320751 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3251812320751 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3341812320751 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (925082402975123894543 / 5000000000000000000000 : ℝ) ≤
      Real.log (19251812320751 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3341812320751 / 16000000000000 : ℝ) ≤
      (-(978797156642601188271 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3341812320751 / 16000000000000 : ℝ) = (3341812320751 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3341812320751 / 2000000000000 : ℝ) ≤
            (320853806419898811729 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4508195537539797 / 10000000000000000 : ℝ) ≤ Real.sqrt (3251812320751 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3251812320751 / 16000000000000 : ℝ) ≤ (22540977687699 / 50000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3251812320751 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau304 :
    Real.arctan (22540977687699 / 50000000000000 : ℝ) ≤
      (132354768328260144823 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (132354768328260144823 / 312500000000000000000 : ℝ)) ≤
      Real.arctan (50000000000000 / 22540977687699 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (50000000000000 / 22540977687699 : ℝ) =
              (22540977687699 / 50000000000000 : ℝ)
            by
        norm_num];
        exact hau304)
  have hz1 :
    (50000000000000 / 22540977687699 : ℝ) ≤ 1 / Real.sqrt (3251812320751 / 16000000000000 : ℝ) := by
    rw [show (50000000000000 / 22540977687699 : ℝ) = 1 / (22540977687699 / 50000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1502731845846599 : ℝ) ≤
      (1648538651467957972391 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3251812320751 / 16000000000000 : ℝ) ≤
      (250000000000000 / 1502731845846599 : ℝ) := by
    rw [show
        (250000000000000 / 1502731845846599 : ℝ) =
          (3 / 40) / (4508195537539797 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (132354768328260144823 / 312500000000000000000 : ℝ)) -
        6 * (1648538651467957972391 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3251812320751 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3251812320751 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4508195537539797 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (132354768328260144823 / 312500000000000000000 : ℝ)) -
          6 * (1648538651467957972391 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (3251812320751 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3251812320751 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3251812320751 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
end

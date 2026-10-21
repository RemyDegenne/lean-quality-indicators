namespace OAI

noncomputable section

namespace ProjectionComparison

open Set

variable {V E : Type*}

variable [Fintype V]

lemma variational (S : System V E) (b v h : V → ℝ) (hp : IsProjection S b v h)
    (k : V → ℝ) (hk : k∈feasible S b) : 0≤∑ x,(h x-v x)*(k x-h x) := by
  let A := ∑ x,(h x-v x)*(k x-h x)
  let T := ∑ x,(k x-h x)^2
  have hT : 0≤T := Finset.sum_nonneg fun x _ => sq_nonneg _
  by_contra hA
  have hA' : A<0 := lt_of_not_ge hA
  let t := min 1 ((-A)/(T+1))
  have ht : 0<t := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
  have ht1 : t≤1 := min_le_left _ _
  have htA : t*(T+1)≤-A := (le_div_iff₀ (by linarith : 0<T+1)).mp (min_le_right _ _)
  have hineq := hp.2 _ (interpolate_feasible S b h k hp.1 hk t ⟨ht.le,ht1⟩)
  rw [objective_interpolate] at hineq
  change objective v h≤objective v h+2*t*A+t^2*T at hineq
  have hn : 2*A+t*T<0 := by linarith
  have hneg := mul_neg_of_pos_of_neg ht hn
  nlinarith [hneg]

end ProjectionComparison
end
end OAI

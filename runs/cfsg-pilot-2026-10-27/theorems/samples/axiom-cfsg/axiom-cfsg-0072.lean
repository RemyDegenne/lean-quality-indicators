public section

namespace CFSG.Sporadic.J4

open Native

theorem parAllR_eq_true {n chunks : ℕ} {p : ℕ → Bool} (h : parAllR n chunks p = true) :
    ∀ i < n, p i = true := by
  intro i hi
  unfold parAllR at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  have hcpos : 0 < chunks + 1 := Nat.succ_pos _
  have hstep := h (i % (chunks + 1)) (Nat.mod_lt _ hcpos)
  change allStepFrom p (i % (chunks + 1)) (chunks + 1)
    ((n + (chunks + 1) - 1 - i % (chunks + 1)) / (chunks + 1)) = true at hstep
  have hdiv := Nat.mod_add_div i (chunks + 1)
  have hk : i / (chunks + 1) < (n + (chunks + 1) - 1 - i % (chunks + 1)) / (chunks + 1) := by
    apply Nat.lt_of_succ_le
    rw [Nat.le_div_iff_mul_le hcpos]
    have hmod := Nat.mod_lt i hcpos
    have e : (i / (chunks + 1) + 1) * (chunks + 1) =
        (chunks + 1) * (i / (chunks + 1)) + (chunks + 1) := by ring
    rw [e]
    generalize (chunks + 1) * (i / (chunks + 1)) = X at hdiv ⊢
    omega
  have := allStepFrom_eq_true hstep _ hk
  rwa [hdiv] at this

end CFSG.Sporadic.J4
end

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance

attribute [local instance] Classical.propDecidable

theorem interval_pair_congruence_bound (J d : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, congruenceIndicator d i j) ≤
      (J : ℝ)^2/d+J := by
  calc
    _ = ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, congruenceIndicator d j i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congruenceIndicator_symm d i j
    _ ≤ ∑ _i ∈ Finset.range J, ((J : ℝ)/d+1) :=
      Finset.sum_le_sum (fun i _ => residue_indicator_bound J d i hd)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end ErdosRandomVariance
end
end Erdos970
end OAI

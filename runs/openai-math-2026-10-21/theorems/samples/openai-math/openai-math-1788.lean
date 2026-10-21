namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace ErdosHyperbola

theorem multiple_reciprocal_sum_le (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), 1/(n : ℝ)) ≤
      (1/(d : ℝ))*harmonicWeight N := by
  let S := (Finset.Icc 1 N).filter (d ∣ ·)
  let f : ℕ → ℕ := fun n => n/d
  have hi : Set.InjOn f (S : Set ℕ) := by
    intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    calc
      a = d*(a/d) := (Nat.mul_div_cancel' ha').symm
      _ = d*(b/d) := by rw [show a/d = b/d from he]
      _ = b := Nat.mul_div_cancel' hb'
  have hsub : S.image f ⊆ Finset.Icc 1 N := by
    intro j hj
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hnI,hnD⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp hnI
    have he := Nat.mul_div_cancel' hnD
    have hjp : 0 < (n/d : ℕ) := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz,mul_zero] at he
      omega
    exact Finset.mem_Icc.mpr ⟨hjp,(Nat.div_le_self n d).trans hnN⟩
  have heq : (∑ n ∈ S, 1/(n : ℝ)) =
      (1/(d : ℝ)) * ∑ j ∈ S.image f, 1/(j : ℝ) := by
    rw [Finset.mul_sum,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnD := (Finset.mem_filter.mp hn).2
      dsimp only [f]
      rw [one_div_mul_one_div,← Nat.cast_mul,Nat.mul_div_cancel' hnD]
    · exact fun a ha b hb he => hi ha hb he
  change (∑ n ∈ S, 1/(n : ℝ)) ≤ _
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

end ErdosHyperbola
end
end Erdos970
end OAI

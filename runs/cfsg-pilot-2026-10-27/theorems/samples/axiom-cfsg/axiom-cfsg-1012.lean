public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

theorem bvec_eq_sum (n m : ℕ) :
    bvec n m = ∑ j ∈ Finset.range n, if m.testBit j then bvec n (2 ^ j) else 0 := by
  funext i
  rw [Finset.sum_apply]
  have h : ∀ j ∈ Finset.range n, (if m.testBit j then bvec n (2 ^ j) else 0) i =
      if (i : ℕ) = j then bvec n m i else 0 := by
    intro j _
    by_cases hij : (i : ℕ) = j
    · subst hij
      by_cases hm : m.testBit i <;> simp [hm, bvec_apply]
    · rw [ite_eq_right hij]
      split_ifs
      · simp [bvec_apply, Ne.symm hij]
      · rfl
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq (Finset.range n) (i : ℕ),
    ite_eq_left (Finset.mem_range.2 i.2)]

end CFSG.Quasithin.H.Mathieu
end

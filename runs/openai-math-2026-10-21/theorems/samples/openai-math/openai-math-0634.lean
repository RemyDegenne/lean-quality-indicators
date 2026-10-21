namespace OAI

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem source_marked_product_stop (n beta : ℕ → ℝ) (marked : ℕ → Prop)
    (count : ℕ) (M : ℝ) (hlast : n count ≤ M) (hanti : Antitone n)
    (hmarked : ∀ j < count, marked j → M < n j) :
    (∏ j ∈ Finset.range (firstMassStop n count M), if marked j then beta j else 1) =
      ∏ j ∈ Finset.range count, if marked j then beta j else 1 := by
  apply Finset.prod_subset (Finset.range_mono (firstMassStop_spec n count M hlast).1)
  intro j hj hnot
  have hstop : firstMassStop n count M ≤ j := by
    have : ¬j < firstMassStop n count M := by simpa only [Finset.mem_range] using hnot
    omega
  have hm : ¬marked j := fun hm =>
    (not_lt_of_ge (firstMassStop_after n count M hlast hanti hstop))
      (hmarked j (Finset.mem_range.mp hj) hm)
  exact ite_eq_right hm

end LipschitzHilbert
end
end OAI

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

namespace CriticalSK

lemma sum_covered_by_shells (B R : Finset ℕ) (S : ℕ → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ b, 0 ≤ f b) (hcover : ∀ b ∈ B, ∃ r ∈ R, b ∈ S r) :
    (∑ b ∈ B, f b) ≤ ∑ r ∈ R, ∑ b ∈ B.filter (fun b => b ∈ S r), f b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨r, hr, hbr⟩ := hcover b hb
  calc
    f b = if b ∈ S r then f b else 0 := by rw [ite_eq_left hbr]
    _ ≤ ∑ x ∈ R, if b ∈ S x then f b else 0 := by
      exact Finset.single_le_sum (f := fun x => if b ∈ S x then f b else 0)
        (fun x _ => by split_ifs <;> first | exact hf b | exact le_rfl) hr

end CriticalSK
end
end OAI

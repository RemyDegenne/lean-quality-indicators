namespace OAI

namespace PolycyclicRecognition

open Filter

open scoped Topology BigOperators

theorem finite_subexponential_envelope {I : Type*} [Fintype I]
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (f : I → ℕ → ℝ) (hf0 : ∀ i n, 0 ≤ f i n)
    (hf : ∀ i, HasSubexponentialUpperBoundSeq scale (f i)) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ i n, f i n ≤ R n := by
  classical
  refine ⟨fun n => ∑ i, f i n, fun n => Finset.sum_nonneg (fun i _ => hf0 i n),
    HasSubexponentialUpperBoundSeq.finset_sum hs Finset.univ f (fun i _ => hf i), ?_⟩
  intro i n
  exact Finset.single_le_sum (fun j _ => hf0 j n) (Finset.mem_univ i)

end PolycyclicRecognition
end OAI

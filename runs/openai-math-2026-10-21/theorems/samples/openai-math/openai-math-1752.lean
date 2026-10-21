namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

lemma baseFlow_row (hs : ∀ i, ∑ a, p i a = 1) (i : I) (s : I → Ω) :
    (∑ t, baseFlow p i s t) = density p s := by
  have h := pushedFlow_row_test (density p) (fun r a => Function.update r i a)
    (fun a b => p i a*p i b) (p i) (fun a => by rw [← Finset.mul_sum,hs, mul_one])
    (fun t => if t=s then 1 else 0)
  change (∑ r, ∑ t, baseFlow p i r t*(if r=s then 1 else 0)) =
    mean p (average p i (fun t => if t=s then 1 else 0)) at h
  rw [mean_average p hs] at h
  simpa [mean,mul_ite,Finset.sum_ite_irrel] using h

end
end MatchingFPRAS.Replica
end OAI

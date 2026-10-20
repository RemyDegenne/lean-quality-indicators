public section

open Fintype

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

namespace Finset

section CommSemiring

variable [CommSemiring R]

section DecidableEq

variable [DecidableEq ι]

lemma sum_prod_piFinset [Fintype ι] (s : Finset κ) (g : ι → κ → R) :
    ∑ f ∈ piFinset fun _ : ι ↦ s, ∏ i, g i (f i) = ∏ i, ∑ j ∈ s, g i j := by
  rw [← prod_univ_sum]

end DecidableEq
end CommSemiring
end Finset
end

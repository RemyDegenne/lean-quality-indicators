public section

open Function

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

namespace Finset

section CommGroup

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

@[to_additive ]
lemma prod_range_div' (f : ℕ → G) (n : ℕ) : (∏ i ∈ range n, f i / f (i + 1)) = f 0 / f n := by
  apply prod_range_induction <;> simp

end CommGroup
end Finset
end

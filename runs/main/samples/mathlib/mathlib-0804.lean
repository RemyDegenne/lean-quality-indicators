public section

variable {α β : Type*}

namespace Set

open scoped Pointwise

section Div

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s t : Set α} {a : α}

@[to_additive]
theorem iInter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_iInter_subset_left ..

end Div
end Set
end

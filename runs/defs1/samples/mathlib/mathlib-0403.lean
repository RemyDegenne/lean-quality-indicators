@[expose] public section

open Set

namespace Filter

variable {α β : Type*} {f g : Filter α} {s t : Set α}

@[inherit_doc]
scoped notation "𝓟" => Filter.principal

@[inherit_doc Filter.Eventually]
notation3 "∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r

@[inherit_doc Filter.Frequently]
notation3 "∃ᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r

syntax:50 (name := eventuallyEqStx) term:51 " =ᶠ[" term "] " term:50 : term

syntax:50 (name := eventuallyLEStx) term:51 " ≤ᶠ[" term "] " term:50 : term

/-- The forward map of a filter -/
def map (m : α → β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs fun _x hx ↦ st hx
  inter_sets hs ht := inter_mem hs ht

end Filter
end

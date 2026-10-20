@[expose] public section

variable {α β γ : Type*} {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

namespace Finset

section DisjiUnion

/-- `disjiUnion s f h` is the set such that `a ∈ disjiUnion s f` iff `a ∈ f i` for some `i ∈ s`.
It is the same as `s.biUnion f`, but it does not require decidable equality on the type. The
hypothesis ensures that the sets are disjoint. -/
def disjiUnion (s : Finset α) (t : α → Finset β) (hf : (s : Set α).PairwiseDisjoint t) : Finset β :=
  ⟨s.val.bind (Finset.val ∘ t), Multiset.nodup_bind.2
    ⟨fun a _ ↦ (t a).nodup, s.nodup.pairwise fun _ ha _ hb hab ↦ disjoint_val.2 <| hf ha hb hab⟩⟩

end DisjiUnion
end Finset
end

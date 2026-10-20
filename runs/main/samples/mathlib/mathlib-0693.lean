@[expose] public section

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*} [CommMonoid α] {f : ι → β → α} {g : β → α}
  {x : β} {s : Set β} {I : Finset ι} [UniformSpace α]

section UniformlyOn

@[to_additive]
lemma HasProdUniformlyOn.congr {f' : ι → β → α}
    (h : HasProdUniformlyOn f g s)
    (hff' : ∀ᶠ (n : Finset ι) in atTop, s.EqOn (∏ i ∈ n, f i ·) (∏ i ∈ n, f' i ·)) :
    HasProdUniformlyOn f' g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr hff')

end UniformlyOn
end
end

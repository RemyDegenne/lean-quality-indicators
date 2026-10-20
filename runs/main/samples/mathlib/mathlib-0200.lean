@[expose] public section

open Function Set

notation3"∑ᶠ " (...) ", " r:67:(scoped f => finsum f) => r

notation3"∏ᶠ " (...) ", " r:67:(scoped f => finprod f) => r

section type

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

@[to_additive]
theorem finprod_eq_prod_of_mulSupport_subset (f : α → M) {s : Finset α} (h : mulSupport f ⊆ s) :
    ∏ᶠ i, f i = ∏ i ∈ s, f i := by
  have A : mulSupport (f ∘ PLift.down) = Equiv.plift.symm '' mulSupport f := by
    rw [mulSupport_comp_eq_preimage]
    exact (Equiv.plift.symm.image_eq_preimage_symm _).symm
  have : mulSupport (f ∘ PLift.down) ⊆ s.map Equiv.plift.symm.toEmbedding := by
    rw [A, Finset.coe_map]
    exact image_mono h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]
  simp only [Finset.prod_map, Equiv.coe_toEmbedding]
  congr

end type
end

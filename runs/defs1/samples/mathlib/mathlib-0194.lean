@[expose] public section

open Function Set

section sort

variable {G M N : Type*} {α ι : Sort*} [CommMonoid M] [CommMonoid N]

section

open scoped Classical in
/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
otherwise. -/
noncomputable irreducible_def finsum (lemma := finsum_def') [AddCommMonoid M] (f : α → M) : M :=
  if h : HasFiniteSupport (f ∘ PLift.down) then ∑ i ∈ h.toFinset, f i.down else 0

end
end sort
end

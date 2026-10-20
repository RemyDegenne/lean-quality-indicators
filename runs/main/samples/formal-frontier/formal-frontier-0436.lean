@[expose] public section

universe u

theorem Submodule.int_span_singleton_ne_top_of_not_surjective_intCast
    {R : Type u} [NonAssocRing R]
    (hℤ : ¬ Function.Surjective (Int.cast : ℤ → R)) (x : R) :
    Submodule.span ℤ ({x} : Set R) ≠ ⊤ := by
  intro hx
  exact hℤ (Submodule.intCast_surjective_of_span_singleton_eq_top hx)

end

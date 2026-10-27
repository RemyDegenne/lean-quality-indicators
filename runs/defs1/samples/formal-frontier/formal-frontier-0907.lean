@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

/-- The full subcategory of coherent modules over `R`.

Its `Abelian` instance is supplied by
`Mathlib.CategoryTheory.Abelian.Subcategory` from the closure instances above. -/
abbrev CoherentModuleCat (R : Type u) [Ring R] :=
  (ModuleCat.isCoherent.{u, v} R).FullSubcategory

end

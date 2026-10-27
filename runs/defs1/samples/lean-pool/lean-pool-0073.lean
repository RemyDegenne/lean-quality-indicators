@[expose] public section

noncomputable section

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory

open CategoryTheory.Limits CategoryTheory.MonoidalPreadditive

universe v u

variable {C : Type u}

section Braided

open scoped Classical in
/-- The matrix morphism that swaps tensor factors using the component braidings. -/
def matBraidHom [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [BraidedCategory C]
    (M N : Mat_ C) : (M ⊗ N : Mat_ C) ⟶ (N ⊗ M : Mat_ C) :=
  fun (i₁, i₂) (j₁, j₂) =>
    if hi : i₂ = j₁ then
      if hj : i₁ = j₂ then
        eqToHom (by subst hi; subst hj; rfl) ≫ (β_ (M.X j₂) (N.X j₁)).hom
      else 0
    else 0

end Braided
end RS
end
end

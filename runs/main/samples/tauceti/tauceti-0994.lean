public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S S' : ShortComplex C}

namespace IsAlmostSplit

theorem isIso_of_isIso_τ₃ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit)
    [IsLocalRing (End S.X₁)] [IsLocalRing (End S'.X₁)] (φ : S ⟶ S') [IsIso φ.τ₃] : IsIso φ := by
  -- Compose `φ` with a comparison morphism running the other way; both composites are the
  -- identity on the right-hand end, hence isomorphisms on the left-hand ends.
  obtain ⟨ψ, hψ⟩ := hS'.exists_hom_τ₃_eq hS (asIso φ.τ₃).symm
  have hmono := hS.shortExact.mono_f
  have hmono' := hS'.shortExact.mono_f
  have hcomp : IsIso ((φ ≫ ψ).τ₁) :=
    hS.isLeftAlmostSplit_f.isIso_τ₁_of_τ₃_eq_id hS.shortExact.exact (φ ≫ ψ) (by simp [hψ])
  have hcomp' : IsIso ((ψ ≫ φ).τ₁) :=
    hS'.isLeftAlmostSplit_f.isIso_τ₁_of_τ₃_eq_id hS'.shortExact.exact (ψ ≫ φ) (by simp [hψ])
  rw [comp_τ₁] at hcomp hcomp'
  -- So `φ.τ₁` has a left and a right inverse, hence is monic and epic, hence invertible.
  have hmf : φ.τ₁ ≫ ψ.τ₁ ≫ inv (φ.τ₁ ≫ ψ.τ₁) = 𝟙 S.X₁ := by
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hef : (inv (ψ.τ₁ ≫ φ.τ₁) ≫ ψ.τ₁) ≫ φ.τ₁ = 𝟙 S'.X₁ := by
    rw [Category.assoc, IsIso.inv_hom_id]
  have : Mono φ.τ₁ := mono_of_mono_fac hmf
  have : Epi φ.τ₁ := epi_of_epi_fac hef
  have : IsIso φ.τ₁ := isIso_of_mono_of_epi φ.τ₁
  have : IsIso φ.τ₂ := isIso₂_of_shortExact_of_isIso₁₃ φ hS.shortExact hS'.shortExact
  exact isIso_of_isIso φ

end IsAlmostSplit
end CategoryTheory.ShortComplex
end

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GH74.GLS.Stage4.Hex

open scoped commutatorElement

namespace SPLNatData

variable {G : Type} [Group G] {F : Type} [Field F] {K₁ X₁ X₂ X₃ X₄ R₂ : Subgroup G}
  {ε : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F} {V : Type} [CommGroup V] {π : ↥R₂ →* V}
  {ρ : ↥K₁ →* MulAut V} {τ : V ≃* Multiplicative (Fin 2 → F)} {w : G}
  (h : SPLNatData K₁ X₁ X₂ X₃ X₄ R₂ ε π ρ τ w)

include h

theorem exists_param [Finite F] {Y : Subgroup G} (hY : Y ≤ R₂) (hYX : X₂ ⊓ Y = ⊥)
    (hcard : Nat.card Y = Nat.card F) (i : Fin 2)
    (hline : ∀ x ∈ Y, ∀ j : Fin 2, j ≠ i → Multiplicative.toAdd (clV R₂ π τ x) j = 0) :
    ∃ y : F → G, (∀ a, y a ∈ Y) ∧ (∀ g ∈ Y, ∃ a, y a = g) ∧
      ∀ a, clV R₂ π τ (y a) = Multiplicative.ofAdd (Pi.single i a) := by
  classical
  let f : ↥Y → F := fun x => Multiplicative.toAdd (clV R₂ π τ x) i
  have hfinj : Function.Injective f := by
    intro x x' hxx
    apply Subtype.ext
    apply h.cl_inj_of_inf hY hYX x.2 x'.2
    apply Multiplicative.toAdd.injective
    funext j
    by_cases hj : j = i
    · subst hj; exact hxx
    · rw [hline x x.2 j hj, hline x' x'.2 j hj]
  have : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hfs : Function.Surjective f := hfinj.surjective_of_finite (Finite.card_eq.mp hcard).some
  choose g hg using hfs
  refine ⟨fun a => (g a : G), fun a => (g a).2, ?_, ?_⟩
  · intro x hx
    refine ⟨f ⟨x, hx⟩, ?_⟩
    have := hfinj (hg (f ⟨x, hx⟩))
    exact congrArg Subtype.val this
  · intro a
    apply Multiplicative.toAdd.injective
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [toAdd_ofAdd, Pi.single_eq_same]
      exact hg a
    · rw [toAdd_ofAdd, Pi.single_eq_of_ne hj]
      exact hline _ (g a).2 j hj

end SPLNatData
end CFSG.GH74.GLS.SP.Local
end

@[expose] public section

universe u v w x

open scoped Pointwise

namespace Module.IsCoherent

theorem of_localizationSpan'
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type w} [∀ (g : s), AddCommGroup (Mₚ g)]
    [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type x} [∀ (g : s), CommRing (Rₚ g)]
    [∀ (g : s), Algebra R (Rₚ g)] [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : ∀ (g : s), M →ₗ[R] Mₚ g)
    [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (f g)]
    (h : ∀ (g : s), Module.IsCoherent (Rₚ g) (Mₚ g)) :
    Module.IsCoherent R M where
  finite := Module.Finite.of_localizationSpan' s hs f fun g ↦ (h g).finite
  finitePresentation_submodule N hN := by
    apply Module.FinitePresentation.of_localizationSpan'
      (Rₚ := Rₚ) (Mₚ := fun g ↦ N.localized' (Rₚ g) (Submonoid.powers g.val) (f g)) s hs
      (fun g ↦ N.toLocalized' (Rₚ g) (Submonoid.powers g.val) (f g))
    intro g
    let _ : Module.IsCoherent (Rₚ g) (Mₚ g) := h g
    have hNlocalized :
        (N.localized' (Rₚ g) (Submonoid.powers g.val) (f g)).FG :=
      N.localized'_fg (Rₚ g) (Submonoid.powers g.val) (f g) hN
    let _ : Module.IsCoherent (Rₚ g)
        (N.localized' (Rₚ g) (Submonoid.powers g.val) (f g)) :=
      Module.IsCoherent.submodule _ hNlocalized
    infer_instance

end Module.IsCoherent
end

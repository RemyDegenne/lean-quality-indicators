public section

universe w v u

open LinearMap hiding id

open DirectSum hiding id_apply

open Finsupp

namespace Module

section OfLiftingProperty

theorem Projective.of_lifting_property' {R : Type u} [Semiring R] {P : Type v}
    [AddCommMonoid P] [Module R P] [Small.{v} R]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (h : ∀ {M : Type v} {N : Type v} [AddCommMonoid M] [AddCommMonoid N]
      [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N),
        Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
    -- then `P` is projective.
    Projective R P := by
  refine of_lifting_property'' (fun p hp ↦ ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

end OfLiftingProperty
end Module
end

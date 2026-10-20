public section

namespace TauCeti

open CategoryTheory LinearMap

universe u v

variable {A : Type u} [Ring A]

namespace AuslanderReitenTranspose

section Lifts

variable {M : Type*} {N : Type*} {P₀ : Type*} {P₁ : Type*} {Q₀ : Type*} {Q₁ : Type*}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Projective A Q₀] [Module.Finite A Q₀]
  [Module.Projective A Q₁] [Module.Finite A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀} {π : P₀ →ₗ[A] M} {ρ : Q₀ →ₗ[A] N}

theorem exists_map_eq (h : AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p) :
    ∃ (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
      (hf : f₀ ∘ₗ p = q ∘ₗ f₁), map f₀ f₁ hf = h := by
  have hp : Function.Exact (p.lcomp Aᵐᵒᵖ A) (mk p) := by
    rw [LinearMap.exact_iff, ker_mk]
  obtain ⟨g₀, g₁, hg₀, hg₁⟩ := exists_lift_projective_presentation
    (p := q.lcomp Aᵐᵒᵖ A) (π := mk q)
    (by ext φ; simp) hp (mk_surjective p) h
  obtain ⟨f₁, rfl⟩ := (opDual_lcomp_bijective (A := A) (P := Q₁) (Q := P₁)).surjective g₀
  obtain ⟨f₀, rfl⟩ := (opDual_lcomp_bijective (A := A) (P := Q₀) (Q := P₀)).surjective g₁
  have hf : f₀ ∘ₗ p = q ∘ₗ f₁ := by
    apply (opDual_lcomp_bijective (A := A) (P := Q₀) (Q := P₁)).injective
    ext φ x
    exact (LinearMap.congr_fun (LinearMap.congr_fun hg₁ φ) x).symm
  refine ⟨f₀, f₁, hf, ?_⟩
  apply hom_ext q
  intro φ
  simpa only [map_mk, LinearMap.comp_apply, lcomp_apply'] using LinearMap.congr_fun hg₀ φ

end Lifts
end AuslanderReitenTranspose
end TauCeti
end

public section

namespace TauCeti

open LinearMap

variable {R : Type*} [Semiring R]

section Presentation

variable {M P₀ P₁ Q₀ Q₁ : Type*} [AddCommMonoid M] [Module R M]
  [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
  [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]
  [Module.Projective R P₀] [Module.Projective R P₁]
  [Module.Projective R Q₀] [Module.Projective R Q₁]

theorem exists_linearEquiv_comp_prodMap_comp_fst_eq {f : P₁ →ₗ[R] P₀} {π : P₀ →ₗ[R] M}
    {g : Q₁ →ₗ[R] Q₀} {ρ : Q₀ →ₗ[R] M} (hf : Function.Exact f π) (hπ : Function.Surjective π)
    (hg : Function.Exact g ρ) (hρ : Function.Surjective ρ) :
    ∃ (e₀ : (P₀ × Q₀) ≃ₗ[R] (P₀ × Q₀))
      (e₁ : ((P₁ × Q₀) × (P₀ × Q₁)) ≃ₗ[R] ((P₁ × Q₀) × (P₀ × Q₁))),
      e₀.toLinearMap ∘ₗ f.prodMap id ∘ₗ fst R (P₁ × Q₀) (P₀ × Q₁) =
        (id : P₀ →ₗ[R] P₀).prodMap g ∘ₗ snd R (P₁ × Q₀) (P₀ × Q₁) ∘ₗ e₁.toLinearMap := by
  -- Schanuel's lemma on the two surjections onto `M`.
  obtain ⟨e₀, he₀⟩ := exists_linearEquiv_comp_fst_eq_comp_snd_comp
    (a := π) (b := ρ) (by rw [range_eq_top.mpr hπ, range_eq_top.mpr hρ])
  -- It carries `ker (π ∘ fst) = range f × Q₀` onto `ker (ρ ∘ snd) = P₀ × range g`.
  have hker : ∀ x : P₀ × Q₀, x ∈ range (f.prodMap (id : Q₀ →ₗ[R] Q₀)) ↔
      e₀ x ∈ range ((id : P₀ →ₗ[R] P₀).prodMap g) := by
    intro x
    have hx := LinearMap.congr_fun he₀ x
    simp only [coe_comp, Function.comp_apply, coe_fst, coe_snd, LinearEquiv.coe_coe] at hx
    rw [range_prodMap, range_prodMap, range_id, range_id, Submodule.mem_prod,
      Submodule.mem_prod, ← hf.linearMap_ker_eq, ← hg.linearMap_ker_eq, mem_ker, mem_ker, hx]
    simp
  -- Schanuel's lemma again, on the two first maps, which now have the same range.
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_comp_fst_eq_comp_snd_comp
    (a := e₀.toLinearMap ∘ₗ f.prodMap (id : Q₀ →ₗ[R] Q₀))
    (b := (id : P₀ →ₗ[R] P₀).prodMap g) <| by
      ext y
      refine ⟨?_, fun hy => ?_⟩
      · rintro ⟨x, rfl⟩
        exact (hker _).mp (mem_range_self _ x)
      · obtain ⟨x, hx⟩ := (hker (e₀.symm y)).mpr (by simpa using hy)
        exact ⟨x, by simp [hx]⟩
  exact ⟨e₀, e₁, he₁⟩

end Presentation
end TauCeti
end

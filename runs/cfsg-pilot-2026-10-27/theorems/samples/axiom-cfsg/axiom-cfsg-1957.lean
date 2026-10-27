public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv

variable {S : Type} [CommGroup S] [Finite S] {ρ : Perm (Fin 7) →* MulAut S}
  {E₀ : Subgroup (Perm (Fin 7))}

omit [Finite S] in
theorem famSub_fixed {F₀ : Subgroup S} {X : List (Perm (Fin 7))}
    (hF : ∀ x ∈ X, ∀ w ∈ F₀, ρ x w = w) {σ : Perm (Fin 7)} {v : S} (hv : v ∈ famSub ρ F₀ σ) :
    ∀ x ∈ X, ρ (σ * x * σ⁻¹) v = v := by
  intro x hx
  have hw : (ρ σ)⁻¹ v ∈ F₀ := mem_famSub.1 hv
  have := hF x hx _ hw
  rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, this]
  simp

end CFSG.QuasithinUnique.B42A57
end

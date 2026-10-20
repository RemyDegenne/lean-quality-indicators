public section

namespace TauCeti

open _root_.Quiver

universe u v

variable (Q : Type u) [Quiver.{v} Q]

variable {Q}

variable (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

@[simp]
theorem reorientHomEquiv_symm_inl {i j : Q} (x : {a : i ⟶ j // ¬ σ a}) :
    (reorientHomEquiv σ i j).symm (Sum.inl x) = reorientKeep σ x.1 x.2 :=
  (rfl)

end TauCeti
end

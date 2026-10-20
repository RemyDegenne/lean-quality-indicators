public section

namespace TauCeti

open _root_.Quiver

universe u v

variable (Q : Type u) [Quiver.{v} Q]

variable {Q}

variable (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

theorem reorientSymmetrify_comp_reorientSymmetrifyInv :
    (reorientSymmetrify σ).comp (reorientSymmetrifyInv σ) = Prefunctor.id _ := by
  refine Prefunctor.ext (fun _ => rfl) fun i j b => ?_
  obtain (⟨a, ha⟩ | ⟨a, ha⟩) | ⟨a, ha⟩ | ⟨a, ha⟩ := b <;>
    simp [reorientSymmetrify, reorientSymmetrifyInv, ha] <;> rfl

end TauCeti
end

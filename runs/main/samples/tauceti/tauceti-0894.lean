public section

namespace TauCeti

open Equiv Equiv.Perm

variable {α β : Type*}

theorem orbitCount_eq_one_of_forall_sameCycle [Nonempty α] {σ : Equiv.Perm α}
    (h : ∀ x y, σ.SameCycle x y) : orbitCount σ = 1 := by
  let _ : Nonempty (Quotient (SameCycle.setoid σ)) :=
    ⟨Quotient.mk _ (Classical.choice (inferInstance : Nonempty α))⟩
  let _ : Subsingleton (Quotient (SameCycle.setoid σ)) :=
    ⟨fun q r => Quotient.inductionOn q fun x => Quotient.inductionOn r fun y =>
      Quotient.sound (h x y)⟩
  exact Nat.card_unique

end TauCeti
end

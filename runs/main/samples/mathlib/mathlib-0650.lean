public section

variable {α β γ δ : Type*} {ι : Sort*}

open Equiv.Perm Function

namespace Set

variable {δ : α → Sort*} (s : Set α) (f g : ∀ i, δ i)

variable [∀ j, Decidable (j ∈ s)]

theorem univ_pi_piecewise_univ {ι : Type*} {α : ι → Type*} (s : Set ι) (t : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s)] : pi univ (s.piecewise t fun _ => univ) = pi s t := by simp

end Set
end

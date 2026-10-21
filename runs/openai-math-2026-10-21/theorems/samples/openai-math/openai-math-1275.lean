namespace OAI

section

namespace ThreeMachine.Structure

section PriorityEncoding

variable {J : Type}

namespace GlobalList

theorem samePriority_key {K : GlobalList J} {rank : J → ℕ} {B : ℕ} {P : Set J}
    (hrank : ∀ x, rank x < B) {x y : J} (hx : x ∈ K.Qual) (hy : y ∈ K.Qual) :
    K.samePriority rank B P x < K.samePriority rank B P y ↔ K.KeyLT rank x y := by
  classical
  simp only [samePriority, ite_eq_left hx, ite_eq_left hy, Nat.add_lt_add_iff_left]
  exact keyValue_lt_iff (hrank x) (hrank y)

end GlobalList
end PriorityEncoding
end ThreeMachine.Structure
end
end OAI

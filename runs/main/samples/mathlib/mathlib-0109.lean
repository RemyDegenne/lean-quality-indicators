public section

open scoped Pointwise

open Equiv.Perm Equiv Set MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace alternatingGroup

theorem stabilizer_ne_top {s : Set α} (hs : s.Nonempty) (hsc : sᶜ.Nontrivial) :
    stabilizer (alternatingGroup α) s ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb, c, hc, hbc⟩ := hsc
  suffices ∃ g, g ∉ stabilizer (alternatingGroup α) s by contrapose! this; simp [this]
  use ⟨Equiv.swap a b * Equiv.swap a c, by aesop⟩
  simp_rw [mem_stabilizer_set, Subgroup.mk_smul, mul_smul, Perm.smul_def]
  grind

end alternatingGroup
end

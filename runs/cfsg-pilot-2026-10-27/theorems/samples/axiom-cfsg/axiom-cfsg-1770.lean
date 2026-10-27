public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv Equiv.Perm MulAction

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {E : Subgroup (Perm Ω)}

theorem fixed_of_card_orbit_eq_one {p : Ω} (h : Nat.card (orbit E p) = 1) :
    ∀ g ∈ E, g p = p := by
  intro g hg
  have hu := Nat.card_eq_one_iff_unique.1 h
  have := hu.1
  have : (⟨g p, ⟨⟨g, hg⟩, rfl⟩⟩ : orbit E p) = ⟨p, mem_orbit_self p⟩ := Subsingleton.elim _ _
  exact congrArg Subtype.val this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
end

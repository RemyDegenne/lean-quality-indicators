public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK

open scoped MatrixGroups

section RuChoiceSec

theorem RuChoice.mem_of_inSpan (P : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    ∀ («gens» : List (Matrix (Fin 3) (Fin 3) (ZMod 2))), (∀ g ∈ «gens», g ∈ P) →
      ∀ A, RuChoice.inSpan «gens» A = true → A ∈ P := by
  intro «gens»
  induction «gens» with
  | nil =>
    intro _ A h
    simp only [RuChoice.inSpan, decide_eq_true_eq] at h
    rw [h]
    exact P.zero_mem
  | cons g gs ih =>
    intro hg A h
    simp only [RuChoice.inSpan, Bool.or_eq_true] at h
    have hgs : ∀ x ∈ gs, x ∈ P := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    rcases h with h | h
    · exact ih hgs A h
    · have h1 := ih hgs (A + g) h
      have hgP := hg g List.mem_cons_self
      have : A = (A + g) + g := by
        rw [add_assoc, RuChoice.mat_add_self, add_zero]
      rw [this]
      exact P.add_mem h1 hgP

end RuChoiceSec
end CFSG.ASVolI
end

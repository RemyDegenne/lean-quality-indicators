public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem le_center_of_chiefTrivial [Finite X] (hX : commutator X = ⊤) {O : Subgroup X}
    [O.Normal] (h : ChiefTrivial O) : O ≤ center X := by
  obtain ⟨n, hn⟩ := exists_commIter_le h _ ⊥ O inferInstance inferInstance bot_le le_rfl le_rfl
  have hcomm : ⁅O, (⊤ : Subgroup X)⁆ = ⊥ :=
    commutator_eq_bot_of_commIter hX n O inferInstance (le_bot_iff.1 hn)
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro g
  have : ⁅o, g⁆ = 1 := by
    have hm : ⁅o, g⁆ ∈ ⁅O, (⊤ : Subgroup X)⁆ := Subgroup.commutator_mem_commutator ho (mem_top g)
    rw [hcomm] at hm
    exact Subgroup.mem_bot.1 hm
  exact (commutatorElement_eq_one_iff_commute.1 this).eq.symm

end CFSG.EvenSporadicStandard.M24Std
end

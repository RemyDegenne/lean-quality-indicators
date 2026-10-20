@[expose] public section

open Set

noncomputable section

namespace OrderClosures

universe u

section BooleanStone

variable (B : Type u) [BooleanAlgebra B]

theorem exists_booleanStonePoint_of_not_le {a b : B} (hab : ¬ a ≤ b) :
    ∃ x : BooleanStone B, x.1 a = true ∧ x.1 b = false := by
  let F : Order.PFilter B := Order.PFilter.principal a
  let I : Order.Ideal B := Order.Ideal.principal b
  have hFI : Disjoint (F : Set B) (I : Set B) := by
    rw [Set.disjoint_left]
    intro c hcF hcI
    exact hab ((Order.PFilter.mem_principal.mp hcF).trans
      (Order.Ideal.mem_principal.mp hcI))
  rcases DistribLattice.prime_ideal_of_disjoint_filter_ideal hFI with
    ⟨J, hJ, hIJ, hFJ⟩
  have hbJ : b ∈ J := hIJ Order.Ideal.mem_principal_self
  have haJ : a ∉ J := by
    intro haJ
    exact Set.disjoint_left.mp hFJ (Order.PFilter.mem_principal.mpr le_rfl) haJ
  refine ⟨booleanStonePointOfPrime B J hJ, ?_, ?_⟩
  · simp [booleanStonePointOfPrime, haJ]
  · simp [booleanStonePointOfPrime, hbJ]

end BooleanStone
end OrderClosures
end
end

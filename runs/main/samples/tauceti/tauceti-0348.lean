public section

namespace TauCeti

open Matrix LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} {n : Type*} [DecidableEq n] [Fintype n]

section Perfect

variable [CommRing R]

theorem lie_slIdeal_slIdeal (htwo : IsUnit (2 : R)) :
    ⁅slIdeal R n, slIdeal R n⁆ = slIdeal R n := by
  obtain ⟨t, ht⟩ := htwo.exists_left_inv
  refine le_antisymm (LieSubmodule.lie_le_right _ _) fun A hA => ?_
  rw [← LieSubmodule.mem_toSubmodule]
  refine mem_of_trace_eq_zero_of_single_mem ?_ ?_ (mem_slIdeal_iff.mp hA)
  · intro p q hpq c
    have hx : single p p (1 : R) - single q q (1 : R) ∈ slIdeal R n := by simp [mem_slIdeal_iff]
    have hy : single p q (t * c) ∈ slIdeal R n := by simp [mem_slIdeal_iff, hpq]
    have h := LieSubmodule.lie_mem_lie hx hy
    rw [lie_single_self_sub_single_self_single hpq, ← mul_assoc, mul_comm (2 : R) t, ht,
      one_mul] at h
    exact h
  · intro p q c
    rcases eq_or_ne p q with rfl | hpq
    · simp
    have hx : single p q c ∈ slIdeal R n := by simp [mem_slIdeal_iff, hpq]
    have hy : single q p (1 : R) ∈ slIdeal R n := by simp [mem_slIdeal_iff, hpq.symm]
    have h := LieSubmodule.lie_mem_lie hx hy
    rw [lie_single_single_eq_sub p q c] at h
    exact h

end Perfect
end TauCeti
end

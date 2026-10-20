public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n : ℕ}

variable (t : PermutationTriple n)

variable (τ : Perm (Fin n))

variable {t}

variable (t)

@[simp] theorem cycleData_swap1Inf :
    (swap1Inf t).cycleData = (t.cycleData.1, t.cycleData.2.2, t.cycleData.2.1) := by
  have h : IsConj t.σinf (t.σ1⁻¹ * t.σinf * t.σ1) := isConj_iff.mpr ⟨t.σ1⁻¹, by group⟩
  rw [partition_eq_of_isConj] at h
  simp [Prod.ext_iff, ← h]

end PermutationTriple
end TauCeti
end

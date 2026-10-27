public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Equiv Equiv.Perm

theorem exists_swap_of_cycleType_two {n : ℕ} {σ : Perm (Fin n)} (h : σ.cycleType = {2}) :
    ∃ i j : Fin n, i ≠ j ∧ σ = swap i j :=
  Perm.isSwap_iff_cycleType.mpr h

end CFSG.GH74.GLS.Stage1.Thm4.L96
end

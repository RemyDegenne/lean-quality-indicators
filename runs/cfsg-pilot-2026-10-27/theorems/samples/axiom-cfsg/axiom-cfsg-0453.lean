public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter CFSG.CGT.PushingUpLit.BHSSym

section Chain

variable {G : Type*} [Group G] {z : G} {m : ℕ}

theorem z_swap_of (hm : 10 ≤ m) (D : NearData z (m + 1)) {i : ℕ} (hi : i < m)
    (Di : NearData (nxs D i) (m + 1)) :
    ∃ τ : Perm (Fin (m + 1)), τ.IsSwap ∧ Di.hom τ = z := by
  have hp : z ∈ Partners (nxs D i) := Partners.symm (nxs_partner D hi)
  have hs := NearData.isSwap_symm (by omega) D Di (nxs_partner D hi) (nxs_π D hi)
  exact NearData.exists_swap_of_isSwap (by omega) Di hp hs

end Chain
end CFSG.OddStandard.AltStdSec
end

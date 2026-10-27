public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)

open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n : ℕ}

section Centralizer

variable {p q : Fin n}

theorem commute_twoCentralElt_iff {g : StatedSp n K} (a b : K) :
    g * twoCentralElt n p q a b = twoCentralElt n p q a b * g ↔
      mat n K g * zHat p q a b = zHat p q a b * mat n K g := by
  rw [← mat_injective.eq_iff, map_mul, map_mul, mat_twoCentralElt_eq_add]
  have e1 : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) + single (Sum.inl p) (Sum.inr p) a +
      single (Sum.inl p) (Sum.inr q) b + single (Sum.inl q) (Sum.inr p) b = 1 + zHat p q a b := by
    rw [zHat]
    abel
  rw [e1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj]

end Centralizer
end CFSG.SeitzReduction.SymplecticPilot
end

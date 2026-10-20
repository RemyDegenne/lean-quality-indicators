namespace P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero

open UpperHalfPlane Filter Complex MulAction MeasureTheory Set

open scoped MatrixGroups Topology ModularForm Real

noncomputable section

namespace LevelOneResidue

scoped instance (x : ℍ) : Finite (stabilizer SL(2, ℤ) x) := (finite_stabilizer x).to_subtype

section Cutoff

local notation "st" => Real.smoothTransition

def boxH (T : ℝ) : Set ℍ := ((↑) : ℍ → ℂ) ⁻¹' box T

end Cutoff
end LevelOneResidue
end
end P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero

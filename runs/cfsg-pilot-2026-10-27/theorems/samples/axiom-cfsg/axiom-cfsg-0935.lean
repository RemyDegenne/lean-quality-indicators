public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal

open CFSG.RankThree.Classical2 (orthDerived)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus
    regular_coordinateQuadMinus)

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

section Coordinates

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_isLongRoot_mem_pairPerp {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    ∃ z ∈ pairPerp (K := K) k, IsLongRoot (coordinateQuadPlus n K) z := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne hn k
  exact exists_isLongRoot_mem_pairPerpOf (regular_coordinateQuadPlus n K hn).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij)

end Coordinates
end CFSG.SeitzReduction.OmegaPilot
end

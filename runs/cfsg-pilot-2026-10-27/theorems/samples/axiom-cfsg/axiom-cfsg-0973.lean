public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup

open CFSG.RankThree.Classical2 (orthDerived)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  matrixDerived matrixProjectiveProjection)

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus plusIndexEquiv)

open CFSG.SeitzReduction.SymplecticPilot (suppGL IsSuppMat mem_suppGL planeCoords)

open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)

section Supp

variable {K : Type} [Field K] {d : ℕ}

variable {Q : QuadraticForm K (Fin d → K)}

theorem projHom_mem_suppBar_of_fix {C : Set (Fin d)} (g : orthDerived Q)
    (hfix : ∀ b, b ∉ C →
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single b 1) = Pi.single b 1)
    (hdual : ∀ a, a ∉ C → ∃ a', a' ∉ C ∧ ∃ β : K, β ≠ 0 ∧
      ∀ v, QuadraticMap.polar Q (Pi.single a' 1) v = β * v a) :
    projHom Q g ∈ suppBar Q C :=
  projHom_mem_suppBar_of_entry g (entry_eq_of_fix
    (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup g.2) hfix hdual)

end Supp
end CFSG.SeitzReduction.OmegaPilot
end

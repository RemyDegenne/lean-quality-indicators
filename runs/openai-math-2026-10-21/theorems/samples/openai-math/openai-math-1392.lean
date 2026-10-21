namespace OAI

noncomputable section

namespace ContinuumCoulomb

open Matrix

open scoped BigOperators InnerProductSpace Classical

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaPhysicalPenalty_high (g : ℝ) (x : EuclideanSpace ℂ (σ × (κ → Fin 2)))
    (hx : qmaMediatorRestriction x = 0) :
    qmaMatrixOperator (qmaPhysicalPenaltyMatrix g) x = qmaPaddedPenalty g x := by
  have he := qmaAncillaDiagonal_real_operator (σ := σ) (κ := κ)
    (fun a => g*qmaAncillaNumber a)
  have hp := congrArg (fun f : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) => f x) he
  change qmaMatrixOperator (qmaPhysicalPenaltyMatrix g) x = _ at hp
  rw [hp]
  ext p
  by_cases ha : p.2 = qmaAncillaVacuum
  · have hzero := congrArg (fun u : EuclideanSpace ℂ σ => u p.1) hx
    rw [qmaMediatorRestriction_apply] at hzero
    change x (p.1,qmaAncillaVacuum) = 0 at hzero
    have hxp : x p = 0 := by
      change x (p.1,p.2) = 0
      rw [ha]
      exact hzero
    simp [qmaPaddedPenalty,diagonalPenalty_apply,hxp]
  · simp [qmaPaddedPenalty,diagonalPenalty_apply,qmaPaddedWeight,qmaPaddedExcitationNumber,ha]

end ContinuumCoulomb
end
end OAI

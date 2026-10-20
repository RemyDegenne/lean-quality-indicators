@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

theorem comparisonPenaltyBlock_le_two_smul_blockDiagonalIdentity
    {α : Real} (hα : 0 <= α) :
    comparisonPenaltyBlock (n := n) α <= (2 * α) • blockDiagonalIdentity n := by
  refine Matrix.le_iff.mpr ?_
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · have hαI : (α • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all α)
    have hnegαI : ((-α) • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all (-α))
    have hpenalty : (comparisonPenaltyBlock (n := n) α).IsHermitian :=
      Matrix.IsHermitian.fromBlocks hαI hnegαI hαI
    have hdiag : ((2 * α) • blockDiagonalIdentity n).IsHermitian := by
      simp [blockDiagonalIdentity_eq_one]
    exact hdiag.sub hpenalty
  · intro q
    let x : Point n := blockPointLeft q
    let y : Point n := blockPointRight q
    have hq : doubledPointToBlockPoint (x, y) = q := by
      ext i
      cases i <;> rfl
    have hdiag :
        dotProduct q (Matrix.mulVec ((2 * α) • blockDiagonalIdentity n) q) =
          (2 * α) * dotProduct q q := by
      simp [blockDiagonalIdentity_eq_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hpen :
        dotProduct q (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) q) =
          2 * quadraticPenalty α x y := by
      have h :=
        blockQuadraticModel_comparisonPenaltyBlock_doubledPoint
          (n := n) α (x, y)
      rw [hq] at h
      have hdot :
          dotProduct (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) q) q =
            dotProduct q (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) q) := by
        exact dotProduct_comm _ _
      rw [blockQuadraticModel, hdot] at h
      nlinarith
    have hself :
        dotProduct q q =
          dotProduct x x + dotProduct y y := by
      rw [← hq]
      simp [doubledPointToBlockPoint, dotProduct, Fintype.sum_sum_type, x, y,
        blockPointLeft, blockPointRight]
    have hpenalty :
        quadraticPenalty α x y = (α / 2) * dotProduct (x - y) (x - y) := by
      rw [quadraticPenalty_apply]
    have hsum_nonneg : 0 <= dotProduct (x + y) (x + y) :=
      dotProduct_self_nonneg (x + y)
    have hnonneg : 0 <= α * dotProduct (x + y) (x + y) :=
      mul_nonneg hα hsum_nonneg
    have hquad :
        (2 * α) * dotProduct q q - 2 * quadraticPenalty α x y =
          α * dotProduct (x + y) (x + y) := by
      rw [hself, hpenalty]
      simp only [dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct]
      ring
    have hdiff :
        star q ⬝ᵥ Matrix.mulVec
            ((2 * α) • blockDiagonalIdentity n - comparisonPenaltyBlock (n := n) α) q =
          (2 * α) * dotProduct q q - 2 * quadraticPenalty α x y := by
      simp [Matrix.sub_mulVec, dotProduct_sub, hdiag, hpen]
    rw [hdiff, hquad]
    exact hnonneg

end ViscositySolns
end

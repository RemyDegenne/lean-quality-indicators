public section

open MonoidAlgebra Representation

open scoped MatrixGroups

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} {n : ℤ}

section Semiring

variable [Semiring k]

open ModularGroup MulOpposite in
@[simp]
theorem mapDomainLinearMap_ofMulAction_op_T_zpow_upperTriangularSum (j : ℤ) :
    mapDomainLinearMap k k (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers T) _))
        (ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (op (T : PSL(2, ℤ)) ^ j)
          (upperTriangularSum k n)) =
      mapDomainLinearMap k k (Quotient.mk _) (upperTriangularSum k n) := by
  -- right multiplication by `T ^ i` keeps matrices upper-triangular, so for `x ∈ ℳₙ^∞` some
  -- `γ i x ∈ ⟨T⟩` moves `x • T ^ i` back into `ℳₙ^∞`
  have key (i : ℤ) (x) (hx : x ∈ upperTriangularReps n) :
      ∃ γ : Subgroup.zpowers T, γ • op (T : PSL(2, ℤ)) ^ i • x ∈ upperTriangularReps n := by
    obtain ⟨A, hA, rfl⟩ := mem_upperTriangularReps.1 hx
    rw [← op_zpow, ← QuotientGroup.mk_zpow, op_smul_mk]
    exact (exists_T_zpow_smul_mk_mem_upperTriangularReps (by rintro rfl; simp at hA)
      (by simp [coe_T_zpow, Matrix.mul_apply, hA.1])).imp'
        (fun m ↦ ⟨T ^ m, Subgroup.zpow_mem_zpowers T m⟩) fun _ ↦ id
  choose! γ hγ using key
  -- as `ℳₙ^∞` meets each orbit at most once, `φ i x = γ i x • x • T ^ i` permutes `ℳₙ^∞`, with
  -- inverse `φ (-i)`
  let φ (i : ℤ) (x : TraceFormulaMatrixModule n) := γ i x • op (T : PSL(2, ℤ)) ^ i • x
  have inv (i : ℤ) (x) (hx : x ∈ upperTriangularReps n) : φ (-i) (φ i x) = x := by
    have h := hγ (-i) _ (hγ i x hx)
    simp only [φ, ← smul_comm (γ i x), smul_smul, ← zpow_add, neg_add_cancel, zpow_zero,
      one_smul] at h ⊢
    exact smul_eq_self_of_mem_upperTriangularReps hx h
  simp only [upperTriangularSum, map_sum, ofMulAction_single, mapDomainLinearMap_single]
  exact Finset.sum_nbij' (φ j) (φ (-j)) (by simpa [φ] using hγ j) (by simpa [φ] using hγ (-j))
    (by simpa using inv j) (by simpa using inv (-j)) fun _ _ ↦ by simp [φ]

end Semiring
end TauCeti.TraceFormulaMatrixModule
end

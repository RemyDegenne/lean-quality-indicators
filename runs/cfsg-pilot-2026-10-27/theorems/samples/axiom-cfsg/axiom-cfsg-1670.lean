public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem rSU_comm_core {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hA : A * mat (rSU h) = mat (rSU h) * A) (a b : HypIndex 2 1) :
    A a b = A (σr a) (σr b) := by
  have k := congrFun (congrFun hA a) (σr b)
  rw [Matrix.mul_apply, Matrix.mul_apply] at k
  simp only [mat_rSU, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at k
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), Finset.sum_eq_single b] at k
  · rwa [ite_eq_left rfl] at k
  · intro l _ hl
    refine ite_eq_right fun hlb => ?_
    exact hl (by rw [← σr_σr l, hlb, σr_σr])
  · simp

end Model
end CFSG.LocalAnalysis.EvenBN.U5
end

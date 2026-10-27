public section

namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral

variable {Γ A : Type*} [Group Γ] [AddCommGroup A] [DistribMulAction Γ A]

theorem pow_smul_of_fix {x : Γ} {a : A} (h : x • (x • a - a) = x • a - a) (k : ℕ) :
    x ^ k • a = a + k • (x • a - a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, smul_add, smul_comm x k, h, succ_nsmul]
    abel

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
end

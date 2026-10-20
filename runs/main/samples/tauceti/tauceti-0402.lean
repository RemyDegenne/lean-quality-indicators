public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

noncomputable section

lemma weightedAbelJacobiQuotientClass_eq_sum (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
      D.sum fun x n => n • S.weightedAbelJacobiQuotientClass w hx₀ (ofPoint x) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero =>
      simp
  | single x n =>
      rw [Finsupp.sum_single_index]
      · rw [single_eq_zsmul_ofPoint x n,
          S.weightedAbelJacobiQuotientClass_zsmul w hx₀ n (ofPoint x)]
      · simp
  | add D E hD hE =>
      rw [S.weightedAbelJacobiQuotientClass_add w hx₀, Finsupp.sum_add_index, hD, hE]
      · intro x
        simp
      · intro x _ b
        simp [add_zsmul]

end
end OrderSystem
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end

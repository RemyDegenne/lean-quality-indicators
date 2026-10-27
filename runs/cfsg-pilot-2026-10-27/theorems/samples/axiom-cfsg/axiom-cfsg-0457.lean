public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix QuadraticMap

open LinearMap (BilinForm)

open CFSG.LieType.Universal.Spin (quadPlus quadOdd quadMinus coe_quadPlus coe_quadOdd
  coe_quadMinus)

open CFSG.GroupTheory.WeirSylow (IsPlusType)

open CFSG.Assembly.LowTwoRank Module Matrix QuadraticMap

open LinearMap (BilinForm)

section Forms

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem two_mul_finrank_le_of_singular [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V} (hW : ∀ x ∈ W, Q x = 0) :
    2 * finrank K W ≤ finrank K V := by
  have h := LinearMap.BilinForm.finrank_orthogonal hQ W
  have hle : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) W := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => by
      change polarBilin Q y x = 0
      rw [polarBilin_apply_apply, QuadraticMap.polar, hW _ (add_mem hy hx), hW y hy, hW x hx,
        sub_zero, sub_zero]
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_le W
  omega

end Forms
end CFSG.Blueprint.EvenSource
end

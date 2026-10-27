public section

namespace CFSG.RankThree.PartOne.StrongP

open Matrix

section Heisenberg

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Nform_mul {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ α' β' γ' : K) :
    Nform a b c α β γ * Nform a b c α' β' γ' =
      Nform a b c (α + α') (β + β') (γ + γ' + α * β') := by
  simp only [Nform, mul_add, add_mul, one_mul, mul_one]
  simp [Matrix.single_mul_single_of_ne _ _ _ _ hab.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hbc.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hac.symm, Matrix.single_mul_single_same,
    Matrix.single_add]
  abel

end Heisenberg
end CFSG.RankThree.PartOne.StrongP
end

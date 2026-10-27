public section

open scoped commutatorElement MatrixGroups

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank SL2Model

namespace E214N

variable {Γ : Type} [Group Γ]

theorem e12_mul_e21_ne {F : Type} [Field F] :
    e12 (1 : F) * e21 1 ≠ e21 1 * e12 1 := by
  intro h
  have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h00

end E214N
end CFSG.Quasithin.SimsE2
end

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover

open scoped MatrixGroups

variable {K : Type} [Field K]

theorem tSL_mulVec_e0 (t : Kˣ × Kˣ) :
    ((tSL t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] =
      (t.1 : K) • ![1, 0, 0] := by
  rw [tSL_mulVec]
  exact KGNat.vec3_eq (by simp) (by simp) (by simp)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
end

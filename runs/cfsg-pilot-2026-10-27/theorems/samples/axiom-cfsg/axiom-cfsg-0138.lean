public section

namespace CFSG.Quasithin.F7Two

open CFSG.GorensteinWalter CFSG.PSL2Table

open scoped MatrixGroups

variable {K : Type} [Field K]

@[simp] theorem coe_matA9' (ν i : K) (hν : ν ≠ 0) :
    (matA9' ν i hν : Matrix (Fin 2) (Fin 2) K) = !![0, -ν; ν⁻¹, i] := rfl

end CFSG.Quasithin.F7Two
end

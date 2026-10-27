public section

namespace CFSG.PSL2Table

open Matrix

open scoped MatrixGroups

open CFSG.TwoRankLowerBound.Helpers

variable {F : Type} [Field F]

theorem unipEquiv_coe (hF : ringChar F ≠ 2) (u : Multiplicative F) :
    ((unipEquiv hF u : unipotent F) : PSL(2, F)) = mk (unip u.toAdd) := rfl

end CFSG.PSL2Table
end

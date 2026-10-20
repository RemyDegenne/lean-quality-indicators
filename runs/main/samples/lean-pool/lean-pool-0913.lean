@[expose] public section

namespace NRR

open scoped BigOperators

variable {p : Nat}

namespace FoxNeuwirthOrderComplex

namespace Realization

theorem continuous_xCoord (i : Fin p) :
    Continuous fun x : Realization p => x.xCoord i := by
  unfold xCoord
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply c).comp continuous_subtype_val).mul continuous_const

end Realization
end FoxNeuwirthOrderComplex
end NRR
end

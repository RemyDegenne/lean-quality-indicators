@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

open IsDedekindDomain Cardinal

noncomputable section

namespace MarkoffRiemannRoch

open _root_.FunctionField

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

local instance instDecidableEqRatFuncAdeleFilter : DecidableEq k⟮X⟯ := Classical.decEq _

local instance instDecidableEqPlaceAAdeleFilter : DecidableEq (PlaceA k K) := Classical.decEq _

local instance adeleFiltAddCommGroup (D' : DivisorA k K) : AddCommGroup (adeleFilt k K D') :=
  Submodule.addCommGroup _

local instance adeleFiltModule (D' : DivisorA k K) : Module k (adeleFilt k K D') :=
  Submodule.module _

theorem finiteAdeleFiltDiff_quotient_add_eq {M N : DivisorA k K}
    (hN : N = M + (N - M)) (hE : IsEffective k K (N - M)) :
    Module.Finite k ((adeleFilt k K N) ⧸
      Submodule.comap (adeleFilt k K N).subtype (adeleFilt k K M)) :=
  hN ▸ finiteAdeleFiltDiff_quotient_add_effective k K M (N - M) hE

end FunctionField.Chart
end MarkoffRiemannRoch
end
end

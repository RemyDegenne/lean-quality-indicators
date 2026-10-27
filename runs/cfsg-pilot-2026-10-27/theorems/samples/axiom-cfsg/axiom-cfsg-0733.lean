public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer

open scoped commutatorElement

section Generic

variable {A A' : Type*} [Group A] [Group A'] (f : A ≃* A')

theorem map_center : (center A).map f.toMonoidHom = center A' :=
  Subgroup.map_center_eq f

end Generic
end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport
end

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {d u₁ z : G}

namespace Data611

variable (D : Data611 G T M L V d u₁ z)

include D

omit [Finite G] D in
theorem ZS_le_V : ch6ZS T L V ≤ V := inf_le_left

end Data611
end CFSG.Quasithin.H13
end

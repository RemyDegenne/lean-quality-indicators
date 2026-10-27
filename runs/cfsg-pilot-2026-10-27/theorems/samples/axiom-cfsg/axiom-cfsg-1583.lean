public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

open scoped Pointwise

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem conjLs_apply
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) (y : Ls s) :
    ((M.conjLs hs hs1 y : Ls s) : G) = (M.bel : G) * y * (M.bel : G)⁻¹ := rfl

end RuDataM
end CFSG.Quasithin.RuType
end

@[expose] public section

open scoped Pointwise

variable {G G' : Type*} [Group G] [Group G'] {H K L : Subgroup G}

namespace Subgroup.Commensurable

protected theorem smul {Φ : Type*} [Group Φ] [MulDistribMulAction Φ G] (φ : Φ)
    (h : H.Commensurable K) : Commensurable (φ • H) (φ • K) :=
  h.map _

end Subgroup.Commensurable
end

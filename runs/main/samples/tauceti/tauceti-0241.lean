public section

namespace TauCeti

open groupCohomology

universe u v

variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]

namespace FactorSet

variable {G M}

namespace Extension

variable {α : FactorSet G M}

@[simp] theorem one_right : (1 : α.Extension).right = 1 := rfl

end Extension
end FactorSet
end TauCeti
end

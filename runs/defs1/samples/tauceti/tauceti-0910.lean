public section

namespace TauCeti

namespace FactorSet

universe u v

variable {G : Type u} {M : Type v} [Group G] [CommGroup M] [MulDistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M]

section Cocycle

variable [IsTopologicalGroup M]

variable {z : G × G → Additive M}

/-- **The factor set named by a normalized continuous `2`-cocycle** of the explicit complex of
continuous cochains. Normalization is a hypothesis rather than a consequence: the cochains of that
complex are not normalized, and `TauCeti.ContCohomology.map_one_fst_of_mem_Z2` only says that the
value at `(1, g)` is the value at `(1, 1)`. -/
def ofMemZ2 (hz : z ∈ ContCohomology.Z2 G (Additive M)) (hz₁ : z (1, 1) = 0) : FactorSet G M where
  toFun p := (z p).toMul
  isMulCocycle₂' g h j := congrArg Additive.toMul ((ContCohomology.mem_Z2_iff.1 hz).2 g h j)
  map_one_one' := congrArg Additive.toMul hz₁

end Cocycle
end FactorSet
end TauCeti
end

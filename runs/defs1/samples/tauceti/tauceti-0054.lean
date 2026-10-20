public section

noncomputable section

open Matrix

namespace TauCeti.SuzukiLieIndex

/-- Scalar extension is an isomorphism from the finite-field preimage onto the Suzuki Steinberg
fixed-point subgroup in the algebraic-closure model. -/
noncomputable def finiteFixedSubgroupEquiv (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    finiteFixedSubgroup m hvalid ≃*
      (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype :=
  ((finiteFixedSubgroup m hvalid).equivMapOfInjective
      (generatorEmbedding m hvalid) (generatorEmbedding_injective m hvalid)).trans
    (MulEquiv.subgroupCongr (map_finiteFixedSubgroup m hvalid))

end TauCeti.SuzukiLieIndex
end
end

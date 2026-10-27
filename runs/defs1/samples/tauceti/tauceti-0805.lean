public section

namespace TauCeti

namespace ReeF4LieIndex

noncomputable section

variable (d : ReeF4LieIndex)

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `F₄` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.rootSubgroupPoints (.inl (finCongr d.rank_eq_four i)) d.1.Closure

end
end ReeF4LieIndex
end TauCeti
end

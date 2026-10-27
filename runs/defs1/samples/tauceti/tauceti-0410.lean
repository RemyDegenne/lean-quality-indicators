public section

namespace TauCeti

namespace TypeALieIndex

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of a type-A carrier. -/
noncomputable def simpleRootSubgroup (d : TypeALieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  SlStd.rootSubgroupPoints d.1.rank (.inl i) d.1.Closure

end TypeALieIndex
end TauCeti
end

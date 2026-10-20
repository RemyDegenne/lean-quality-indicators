@[expose] public section

namespace Supernatural

/-- The supernatural index of a closed subgroup of a profinite group. -/
noncomputable def profiniteIndex {G : ProfiniteGrp} (H : ClosedSubgroup G) : Supernatural :=
  ⨆ U : OpenNormalSubgroup G,
    ofFiniteIndex (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup))

end Supernatural
end

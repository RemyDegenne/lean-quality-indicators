@[expose] public section

namespace Supernatural

/-- The relative index of the images of two closed subgroups in a finite
quotient. -/
noncomputable def finiteQuotientRelIndex {G : ProfiniteGrp}
    (N H : ClosedSubgroup G) (U : OpenNormalSubgroup G) : Supernatural :=
  let _ :
      (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).IsFiniteRelIndex
        (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  ofPNat ⟨
    (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).relIndex
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)),
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero⟩

end Supernatural
end

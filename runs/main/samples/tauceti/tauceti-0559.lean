public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X : Type*} {G : Type*} [AddCommGroup G] (S : OrderSystem X G)

namespace OrderSystem

@[simp]
lemma coe_classGroupQuotientPicZeroEquivDegreeRange_mk (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (c : S.ClassGroup) :
    (S.classGroupQuotientPicZeroEquivDegreeRange w h (QuotientAddGroup.mk c) : ℤ) =
      weightedDegreeClass w h c :=
  rfl

end OrderSystem
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end

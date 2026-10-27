public section

open IsDedekindDomain NumberField

open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- The subgroup of real sign patterns realized by units of the ring of integers. -/
noncomputable def integerUnitSignatures :
    Subgroup ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) :=
  -- Supplying the product group explicitly keeps the `MulOne` projection definitionally aligned
  -- with the one carried by `unitSignature`.
  @MonoidHom.range (RingOfIntegers K)ˣ inferInstance
    ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) Pi.group
    (NumberField.unitSignature (K := K))

end TauCeti.GlobalNumberFields
end

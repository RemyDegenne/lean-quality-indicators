public section

open IntermediateField

namespace TauCeti

open AlgebraicGeometry

open scoped IntermediateField.algebraAdjoinAdjoin

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- **The degree-zero divisors map onto `Cl⁰(F)`**, a divisor going to its class. This is the
order system's `weightedDegreeZeroClassHom` at the residue-degree weights, precomposed with the
identification of the two degree-zero subgroups; no divisor-class reasoning is redone here. -/
noncomputable def degreeZeroClassHom (hF : IsFunctionField k F) :
    (degree (k := k) (F := F)).ker →+ (degreeClass hF).ker :=
  ((Place.orderSystem hF).weightedDegreeZeroClassHom (fun P ↦ (P.degree : ℤ))
      (Place.isWeightedDegreeZero_orderSystem hF)).comp
    (AddSubgroup.inclusion ker_degree_eq_weightedDegreeZeroSubgroup.le)

end Divisor
end TauCeti
end

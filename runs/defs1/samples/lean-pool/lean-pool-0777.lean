@[expose] public section

namespace UnrestrictedBooleanMul

namespace N4

noncomputable section

/-- The product of the two leading input coefficients. -/
def sliceInfinityQuadraticANF : ANF 8 :=
  linearANF (placeA 2) * linearANF (placeB 2)

end
end N4
end UnrestrictedBooleanMul
end

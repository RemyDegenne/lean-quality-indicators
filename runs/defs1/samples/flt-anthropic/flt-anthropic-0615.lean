set_option autoImplicit false

namespace ModularCurve

namespace NodeLocalized

noncomputable section

def jRing (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subring.closure (Set.range (CharPReduction.constSeries (coeffSubring A K)) ∪ {jqModC (AlgebraicClosure ℚ)})

end
end NodeLocalized
end ModularCurve

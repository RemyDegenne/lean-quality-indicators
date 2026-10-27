@[expose] public section

namespace UnrestrictedBooleanMul

namespace N4

noncomputable section

/-- The correlated first-jet state after moving its selected place to zero.
The seed representative uses the very same linear form whose nonzero
first-jet component was obtained in `FirstJetSupport`. -/
def ZeroNormalizedFirstJetState (C : Circuit 8 8) : Prop :=
  ∃ (theta : Fin 3) (eps : F₂) (anchorLinear companionLinear : LinearForm)
    (correction : ANF 8) (pa pb ja jb : F₂),
    correction ∈ rationalLowSpace ∧
    anfPlaceNormalize theta (C.gate 3) + correction =
      linearANF anchorLinear *
        (linearANF companionLinear +
          rationalANF (rationalSingleton 0)) ∧
    vectorWedgeTwo anchorLinear (rationalPlaceTwo 0) ≠ 0 ∧
    anchorLinear = normalizedFirstJetVector pa pb ja jb ∧
    (ja ≠ 0 ∨ jb ≠ 0) ∧
    circuitFlag C 5 = circuitFlag C 4 ⊔
      Submodule.span F₂ {targetANF (rationalTangentAt theta eps)}

end
end N4
end UnrestrictedBooleanMul
end

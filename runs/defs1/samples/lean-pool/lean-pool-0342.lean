@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- The first coordinate function, regarded as an element of its generated subfield. -/
def firstCoordinateInSubfield
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :
    FirstCoordinateSubfield f :=
  ⟨planeCurveFunction f 0,
    IntermediateField.mem_adjoin_simple_self K (planeCurveFunction f 0)⟩

end
end BGS.CorvajaZannier
end

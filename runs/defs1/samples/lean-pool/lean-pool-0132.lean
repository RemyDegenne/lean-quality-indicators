@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace GerverSofa.PartF

/-- The composition currently implemented upstream: `q ↦ R q + p`. -/
def rotateThenTranslate (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) : Rigid :=
  R.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ p)

end GerverSofa.PartF
end
end
end
end
end
end
end
end

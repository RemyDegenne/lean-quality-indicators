set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace StableGL

/-- The existing quotient determinant, with inverse the existing rank-one section,
identifies stable elementary classes with coefficient units over a local ring. -/
noncomputable def quotientDetMulEquiv (R : Type u) [CommRing R] [IsLocalRing R] :
    (StableGL R ⧸ stableElementarySubgroup R) ≃* Rˣ where
  toFun := quotientDet R
  invFun := quotientRankOneUnits R
  left_inv := by
    intro quotient
    apply ((quotientDet R).ker_eq_bot_iff.mp (quotientDet_ker_eq_bot_local R))
    exact quotientDet_quotientRankOneUnits R (quotientDet R quotient)
  right_inv := quotientDet_quotientRankOneUnits R
  map_mul' := (quotientDet R).map_mul

end StableGL
end LocalRing
end Matrix.GeneralLinearGroup
end

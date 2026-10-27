set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

namespace StableGL

universe u v

/-- The determinant induced on the existing stable elementary quotient. -/
noncomputable def quotientDet (R : Type u) [CommRing R] :
    (StableGL R ⧸ stableElementarySubgroup R) →* Rˣ :=
  QuotientGroup.lift (stableElementarySubgroup R) (det R) (elementary_le_ker_det R)

end StableGL
end Matrix.GeneralLinearGroup
end

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

namespace StableGL

universe u v

/-- The determinant factored through the canonical abelianization. -/
noncomputable def abelianizationDet (R : Type u) [CommRing R] :
    Abelianization (StableGL R) →* Rˣ :=
  Abelianization.lift (det R)

end StableGL
end Matrix.GeneralLinearGroup
end

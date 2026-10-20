set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

namespace StableGL

universe u v

/-- Rank-one units projected to the abelianization, over any semiring. -/
noncomputable def abelianizationRankOneUnits (R : Type u) [Semiring R] :
    Rˣ →* Abelianization (StableGL R) :=
  Abelianization.of.comp (rankOneUnits R)

end StableGL
end Matrix.GeneralLinearGroup
end

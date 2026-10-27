public section

noncomputable section

open ValuativeRel

namespace TauCeti

open scoped zHat

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The marked generator `σ` of the Iwasawa group, the image of an arithmetic Frobenius. -/
abbrev iwasawaSigma : IwasawaGroup K :=
  presentedProfiniteGroup.of {iwasawaRelator K} (ULift.up 0)

end TauCeti
end
end

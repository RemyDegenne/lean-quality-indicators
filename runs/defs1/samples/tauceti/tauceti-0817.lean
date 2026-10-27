public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

noncomputable local instance instFintypeResidueField : Fintype 𝓀[K] := Fintype.ofFinite _

namespace Units

/-- The sign of the quadratic character of the reduction of an integral unit. -/
noncomputable def oddResidueSign (u : 𝒪[K]ˣ) : ℤˣ := by
  classical
  exact if IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) then 1 else -1

end Units
end TauCeti
end

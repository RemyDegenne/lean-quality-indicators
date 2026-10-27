public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer

open _root_.ValuativeRel

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The source of the local class-field correspondence: open subgroups of finite index in `Kˣ`. -/
abbrev LocalNormSubgroups (K : Type) [Field K] [TopologicalSpace K] : Type :=
  {N : OpenSubgroup Kˣ // N.toSubgroup.FiniteIndex}

end TauCeti.ClassFieldTheory
end

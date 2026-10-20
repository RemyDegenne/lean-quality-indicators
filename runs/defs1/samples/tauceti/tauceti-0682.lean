public section

noncomputable section

namespace TauCeti.ClassFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable {K}

variable (K)

/-- The inclusion `W_K → G_K` of the Weil group into the absolute Galois group. -/
def weilToAbsolute : WeilGroup K →* Field.absoluteGaloisGroup K :=
  (localWeilGroup K).subtype

end TauCeti.ClassFieldTheory
end
end

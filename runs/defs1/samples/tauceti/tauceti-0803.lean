public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

section Core

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]

section Tame

variable (K L)

/-- An extension of nonarchimedean local fields is **tamely ramified** when the residue
characteristic does not divide its ramification index. For a general valued field tameness also
asks for a separable residue extension; that condition is automatic here, the residue fields of
nonarchimedean local fields being finite. -/
def IsTamelyRamified : Prop :=
  ¬ ringChar 𝓀[K] ∣ ramificationIndex K L

end Tame
end Core
end TauCeti
end
end

@[expose] public section

universe uR uS uT uM uN uP uY

open CategoryTheory

namespace TopModuleCat

section Restriction

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable [TopologicalSpace R] [TopologicalSpace S]

variable (φ : R →+* S) (hφ : Continuous φ)

@[simp]
theorem restrictScalarsObj_smul (M : TopModuleCat.{uM} S) (r : R) (x : M) :
    r • (show restrictScalarsObj φ hφ M from x) =
      (show restrictScalarsObj φ hφ M from φ r • x) := rfl

end Restriction
end TopModuleCat
end

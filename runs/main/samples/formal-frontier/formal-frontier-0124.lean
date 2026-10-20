@[expose] public section

universe uR uS uT uM uN uP uY

open CategoryTheory

namespace TopModuleCat

section Composition

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

variable [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T]

variable (φ : R →+* S) (ψ : S →+* T) (hφ : Continuous φ) (hψ : Continuous ψ)

@[simp]
theorem restrictScalarsCompIso_inv_apply (M : TopModuleCat.{uM} T) (x : M) :
    (restrictScalarsCompIso φ ψ hφ hψ M).inv x = x := rfl

end Composition
end TopModuleCat
end

@[expose] public section

universe uR uS uT uM uN uP uY

open CategoryTheory

namespace TopModuleCat

section Composition

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

variable [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T]

variable (φ : R →+* S) (ψ : S →+* T) (hφ : Continuous φ) (hψ : Continuous ψ)

/-- Restriction along a composite is isomorphic to successive restriction.
The algebraic comparison is Mathlib's, and both carrier functions are identities. -/
noncomputable def restrictScalarsCompIso (M : TopModuleCat.{uM} T) :
    restrictScalarsObj (ψ.comp φ) (hψ.comp hφ) M ≅
      restrictScalarsObj φ hφ (restrictScalarsObj ψ hψ M) :=
  ofIso
    { __ := ((ModuleCat.restrictScalarsComp φ ψ).app M.toModuleCat).toLinearEquiv
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }

end Composition
end TopModuleCat
end

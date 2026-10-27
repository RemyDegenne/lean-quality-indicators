@[expose] public section

open CategoryTheory Function

namespace Profinite.FinitePresentation

universe u

variable {X Y : Profinite.{u}} (f : X ⟶ Y)

/-- The reindexed source cone is a limit cone when `f` is injective. -/
noncomputable def injectiveSourceLimit (hf : Injective f) :
    Limits.IsLimit (injectiveSourceCone f) := by
  letI := injectiveIndex_initial f hf
  exact (Functor.Initial.isLimitWhiskerEquiv (injectiveIndex f) X.asLimitCone).symm X.asLimit

end Profinite.FinitePresentation
end

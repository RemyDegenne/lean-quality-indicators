section

def ContinuousMulEquiv.units_map {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [Monoid M] [Monoid N] (f : M ≃ₜ* N) : Mˣ ≃ₜ* Nˣ :=
  {
  __ := Units.mapEquiv f
  continuous_toFun := by apply Continuous.units_map _ f.continuous_toFun
  continuous_invFun := by apply Continuous.units_map _ f.continuous_invFun
      }

end

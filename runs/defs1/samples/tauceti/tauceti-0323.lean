public section

namespace PowerSeries

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R⟦X⟧ M] [Module R M]

variable [IsScalarTower R R⟦X⟧ M]

variable (R) in
/-- The derivation of `R⟦X⟧` taking the value `m` at `X`, namely `f ↦ f' • m`. -/
noncomputable def mkDerivation : M →ₗ[R⟦X⟧] Derivation R R⟦X⟧ M where
  toFun m := (LinearMap.toSpanSingleton R⟦X⟧ M m).compDer d⁄dX
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by
    ext
    exact smul_comm _ _ _

end PowerSeries
end

public section

namespace PowerSeries

variable (R : Type*) [CommSemiring R]

/-- The Mahler derivation `(1 + X) d/dX` of `R⟦X⟧`. It is `Y d/dY` in the variable
`Y = 1 + X`, and under the Amice transform it corresponds to multiplying a measure on `ℤ_p` by the
coordinate function. -/
noncomputable def mahlerDerivation : Derivation R R⟦X⟧ R⟦X⟧ := (1 + X : R⟦X⟧) • derivative

end PowerSeries
end

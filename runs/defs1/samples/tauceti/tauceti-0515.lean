public section

namespace TauCeti

namespace PadicInt

open Multiplicative

variable {p : ℕ} [Fact p.Prime]

/-- **Continuous automorphisms of `ℤ_p`.** The topological group isomorphism from the continuous
automorphisms of the additive group of `ℤ_[p]`, with the congruence topology, to the units of
`ℤ_[p]`, sending an automorphism to its value at `1`
(`TauCeti.PadicInt.coe_continuousAutEquivUnits_apply`). Its inverse sends a unit `u` to
multiplication by `u` (`TauCeti.PadicInt.continuousAutEquivUnits_symm_apply`). -/
noncomputable def continuousAutEquivUnits : ContinuousAut (Multiplicative ℤ_[p]) ≃ₜ* ℤ_[p]ˣ :=
  Peripheral.continuousAutEquivUnits (isProP_multiplicative_padicInt p)
    (freeProP.equivPadicInt p (Fin 1)).symm

end PadicInt
end TauCeti
end

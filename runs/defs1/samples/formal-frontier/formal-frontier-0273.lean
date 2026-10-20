set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

namespace TopologicalPowerQuotient

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [CommGroup A] [CommGroup B] [CommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]

/-- The canonical continuous multiplicative quotient homomorphism. -/
def mkQ (n : ℕ) : A →ₜ* TopologicalPowerQuotient A n where
  toMonoidHom := QuotientGroup.mk' (closedPowers A n)
  continuous_toFun := QuotientGroup.continuous_mk

end TopologicalPowerQuotient
end
end

set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

namespace TopologicalPowerQuotient

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [CommGroup A] [CommGroup B] [CommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]

/-- Functoriality of the multiplicative closed-power quotient. -/
def map (n : ℕ) (f : A →ₜ* B) :
    TopologicalPowerQuotient A n →ₜ* TopologicalPowerQuotient B n where
  toMonoidHom := QuotientGroup.lift (closedPowers A n) ((mkQ n).comp f) (by
    intro x hx
    exact (QuotientGroup.eq_one_iff (f x)).mpr
      (map_closedPowers_le n f hx))
  continuous_toFun := by
    rw [(QuotientGroup.isQuotientMap_mk
      (closedPowers A n)).continuous_iff]
    exact (mkQ n).continuous.comp f.continuous

end TopologicalPowerQuotient
end
end

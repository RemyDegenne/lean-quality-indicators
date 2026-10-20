@[expose] public section

namespace BGS.NumberTheory

namespace PrimePowerFactor

/-- A factor is meaningful when its base is prime and its exponent is
positive. -/
def Valid (factor : PrimePowerFactor) : Prop :=
  factor.prime.Prime ∧ 0 < factor.exponent

end PrimePowerFactor
end BGS.NumberTheory
end

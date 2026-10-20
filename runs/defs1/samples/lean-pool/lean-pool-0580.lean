@[expose] public section

namespace NRR

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace RelativeSubdivisionEndpointCollar

open ExplicitAffineRelativeCollar

open ExplicitAffineRelativeCollarCompose

open ExplicitAffineRelativeCollarReverse

variable {p : Nat}

/-- Compose two existential collar witnesses. -/
noncomputable def composeWitness
    {hp : Nat.Prime p} {N₀ Nmid N₁ : Nat}
    (C : Witness hp N₀ Nmid) (D : Witness hp Nmid N₁) :
    Witness hp N₀ N₁ where
  commonLevel := max C.commonLevel D.commonLevel
  timeLevel := C.timeLevel + D.timeLevel + 1
  collar := endpointIdentifiedCollar C.collar D.collar

end RelativeSubdivisionEndpointCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end

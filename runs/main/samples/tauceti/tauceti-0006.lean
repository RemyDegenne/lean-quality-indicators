public section

open scoped Pointwise

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

theorem evenSublattice_carrier_submoduleOf :
    L.evenSublattice.carrier.submoduleOf L.carrier = L.evenSubmodule := by
  rw [evenSublattice_carrier, Submodule.submoduleOf,
    Submodule.comap_map_eq_of_injective L.carrier.injective_subtype]

end TauCeti.IntegralLattice
end

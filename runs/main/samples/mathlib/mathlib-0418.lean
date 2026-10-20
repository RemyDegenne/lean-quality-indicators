@[expose] public section

open Submodule

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)

variable {M : Type*} [AddCommGroup M] [Module R M]

namespace AdicCompletion

@[local simp]
theorem transitionMap_map_one {m n : ℕ} (hmn : m ≤ n) : transitionMap I R hmn 1 = 1 :=
  rfl

end AdicCompletion
end

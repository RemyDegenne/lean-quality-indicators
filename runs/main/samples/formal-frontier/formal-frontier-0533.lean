@[expose] public section

open Filter

open scoped Topology

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

variable (I : Ideal R) [IsAdicComplete I R]

variable (p : ℕ) [Fact p.Prime] (hpI : (p : R) ∈ I)

local notation "K" => MonoidHom.ker (Units.map (RingHom.toMonoidHom (Ideal.Quotient.mk I)))

@[simp] theorem padicPow_zero (v : K) : I.padicPow p hpI 0 v = 1 := by
  exact (I.padicPow_laws p hpI).1 v

end Ideal
end

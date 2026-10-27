@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The parametrization from the full Hankel quotient to the full target
polynomial ring, with its coefficient algebra structure. -/
noncomputable def quotientMap : (Source R n ⧸ hankelIdeal R n) →ₐ[R] Target R :=
  Ideal.Quotient.liftₐ (hankelIdeal R n)
    (AddMonoidAlgebra.mapDomainAlgHom R R (rncExponent n))
    (fun p hp => RingHom.mem_ker.mp (hankelIdeal_le_ker R n hp))

end ToricIdeals.RationalNormalCurve
end

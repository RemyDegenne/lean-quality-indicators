public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

open Classical in
/-- The normalized positive Smith invariant factors of a nondegenerate Gram matrix. -/
noncomputable def gramSmithInvariantFactors (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) : Fin (Fintype.card ι) → ℤ :=
  (L.gramSmithWitness b).choose_spec.choose_spec.choose

end TauCeti.IntegralLattice
end

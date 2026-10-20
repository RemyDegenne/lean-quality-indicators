public section

open Module

namespace TauCeti

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

section DeterminantCriteria

variable (L : IntegralLattice V) [L.IsNondegenerate]

theorem isUnimodular_iff_natAbs_gramDet_eq_one {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.IsUnimodular ↔ (L.gramDet e).natAbs = 1 := by
  rw [L.isUnimodular_iff_discriminant_eq_one,
    L.discriminant_eq_natAbs_gramDet e]

end DeterminantCriteria
end IntegralLattice
end TauCeti
end

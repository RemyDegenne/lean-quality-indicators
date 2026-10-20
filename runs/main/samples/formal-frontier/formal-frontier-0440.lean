@[expose] public section

namespace ToricIdeals.RationalNormalCurve

open MvPolynomial

noncomputable section

universe u v

theorem mem_quotientHomogeneousSubmodule_iff (R : Type u) [CommRing R] (n d : ℕ)
    (x : Source R n ⧸ hankelIdeal R n) :
    x ∈ quotientHomogeneousSubmodule R n d ↔ ∃ p : Source R n,
      p.IsHomogeneous d ∧ Ideal.Quotient.mkₐ R (hankelIdeal R n) p = x :=
  Submodule.mem_map

end
end ToricIdeals.RationalNormalCurve
end

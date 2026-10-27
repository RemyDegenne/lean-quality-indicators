public section

open QuadraticMap

open scoped Matrix

universe u v w

namespace QuadraticMap

section Det

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]

variable {Q : QuadraticMap R M N}

/-- The determinant kernel inside `O(Q)` is canonically isomorphic to `SO(Q)`. -/
noncomputable def specialOrthogonalWithinEquiv (Q : QuadraticMap R M N) :
    specialOrthogonalWithin Q ≃* TauCeti.QuadraticMap.specialOrthogonalGroup Q :=
  (MulEquiv.subgroupCongr specialOrthogonalWithin_eq_subgroupOf).trans
    (Subgroup.subgroupOfEquivOfLe
      (TauCeti.QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q))

end Det
end QuadraticMap
end

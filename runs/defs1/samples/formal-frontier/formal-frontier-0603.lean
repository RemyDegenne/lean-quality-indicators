public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The differential entering degree `-1` in the Tate complex, identified with
the concrete degree-zero group-homology differential. -/
@[expose]
noncomputable def tateDNegTwoArrowIso (M : Rep R G) :
    Arrow.mk ((tateComplex M).d (-2) (-1)) ≅ Arrow.mk (groupHomology.shortComplexH0 M).f :=
  Arrow.isoMk (groupHomology.chainsIso₁ M) (groupHomology.chainsIso₀ M) (by
    change (groupHomology.chainsIso₁ M).hom ≫ groupHomology.d₁₀ M =
      (groupHomology.inhomogeneousChains M).d 1 0 ≫
        (groupHomology.chainsIso₀ M).hom
    exact groupHomology.comp_d₁₀_eq M)

end FiniteGroupTateCohomology
end

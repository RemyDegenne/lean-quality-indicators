@[expose] public section

open Module Polynomial

noncomputable section

universe u v

section CommRing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {f : R[X]}

namespace IsAdjoinRoot

variable (h : IsAdjoinRoot S f)

section mkOfAdjoinEqTop

variable [IsDomain R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R]
    {α : S} (hα : IsIntegral R α) (hα₂ : Algebra.adjoin R {α} = ⊤)

/-- If `α` generates `S` as an algebra, then `S` is given by adjoining a root of `minpoly R α`. -/
@[simps]
def mkOfAdjoinEqTop : IsAdjoinRoot S (minpoly R α) where
  map := aeval α
  map_surjective := by
    rw [← Set.range_eq_univ, ← AlgHom.coe_range, ← Algebra.adjoin_singleton_eq_range_aeval,
      hα₂, Algebra.coe_top]
  ker_map := by
    ext
    simpa [Ideal.mem_span_singleton] using minpoly.isIntegrallyClosed_dvd_iff hα _

end mkOfAdjoinEqTop
end IsAdjoinRoot
end CommRing
end
end

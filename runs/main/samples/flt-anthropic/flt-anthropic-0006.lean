namespace P2MW.S_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries

set_option autoImplicit false

namespace RedHomAux

variable {A : Type} [CommRing A] {R : Type} [CommRing R]

theorem emb_add (φ : A →+* R) (x y : PowerSeries A) :
    HahnSeries.ofPowerSeries ℤ R ((x + y).map φ) =
      HahnSeries.ofPowerSeries ℤ R (x.map φ) + HahnSeries.ofPowerSeries ℤ R (y.map φ) := by
  rw [map_add, map_add]

end RedHomAux
end P2MW.S_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries

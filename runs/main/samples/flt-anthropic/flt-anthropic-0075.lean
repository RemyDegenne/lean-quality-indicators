namespace P2MW.S_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular

open Finset

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace Koszul

open Finset CliffordAlgebra ExteriorAlgebra Set.powersetCard

universe u v u' v'

section Exterior

variable {R : Type u'} [CommRing R] {M : Type v'} [AddCommGroup M] [Module R M]

variable {I : Type} [LinearOrder I] {n : ℕ}

theorem koszulD_basis (b : Module.Basis I R M) (d : Module.Dual R M) (s : Set.powersetCard I (n + 1)) :
    koszulD d n (b.exteriorPower (n + 1) s) =
      ∑ k : Fin (n + 1), ((-1 : R) ^ (k : ℕ) * d (b (ofFinEmbEquiv.symm s k))) •
        b.exteriorPower n (eraseNth s k) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, koszulD_ιMulti]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, Function.comp_apply,
    coe_ofFinEmbEquiv_symm_eraseNth]
  rfl

end Exterior
end Koszul
end P2MW.S_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular

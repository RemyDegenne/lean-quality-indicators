public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

theorem sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero (v : Q)
    (y : preprojectiveAlgebra k Q) :
    ∑ i : Symmetrify Q, ∑ b : i ⟶ Symmetrify.of.obj v, preprojectiveMk k Q (ofArrow b) *
      (doubledArrowSign k b • (preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y)) = 0 :=
  sum_map_ofArrow_mul_smul_map_ofArrow_reverse_mul_eq_zero (R := Symmetrify Q) k
    (r := localPreprojectiveRelator k (Q := Q))
    (fun u => localPreprojectiveRelator_eq_sum_ofArrow_mul (Q := Q) k u)
    (fun u => preprojectiveMk_localPreprojectiveRelator (Q := Q) k u)
    (Symmetrify.of.obj (V := Q) v) y

end TauCeti
end

namespace OAI

namespace RationalHitting.Expansion

open Polynomial Module

open scoped BigOperators Polynomial

noncomputable section

theorem wronskian_order_bound {K : Type*} [Field K] [CharZero K]
    (d : ℕ) {V : Submodule K K[X]} {h w : ℕ}
    (b : Basis (Fin h) K V) (a : Fin w → K) (ha : Function.Injective a)
    (e : Fin w → Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d)
    (he : ∀ i, Function.Injective (fun j => (e i j : K[X]).rootMultiplicity (a i))) :
    ∑ i, ∑ j, (e i j : K[X]).rootMultiplicity (a i) ≤
      h * (d - 1) + w * (∑ j : Fin h, j.val) := by
  classical
  have localOrder : ∀ i, ∑ j, (e i j : K[X]).rootMultiplicity (a i) =
      (wronskian (fun j => (b j : K[X]))).rootMultiplicity (a i) +
        (∑ j : Fin h, j.val) := by
    intro i
    rw [← wronskian_order_at (a i) _ (fun j hz => (e i).ne_zero j (Subtype.ext hz)) (he i),
      wronskian_basis_rootMultiplicity d b (e i) (a i) hV]
  simp_rw [localOrder]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  apply Nat.add_le_add_right
  let W := wronskian (fun j => (b j : K[X]))
  have hsum : (∑ i, W.rootMultiplicity (a i)) =
      ∑ x ∈ Finset.univ.image a, W.rootMultiplicity x := by
    rw [Finset.sum_image]
    exact fun i _ j _ hij => ha hij
  rw [hsum]
  apply (sum_rootMultiplicity_le_natDegree W _).trans
  apply natDegree_wronskian_le
  intro j
  have hh := hV (b j) (b j).property (fun hz => b.ne_zero j (Subtype.ext hz))
  omega

end
end RationalHitting.Expansion
end OAI

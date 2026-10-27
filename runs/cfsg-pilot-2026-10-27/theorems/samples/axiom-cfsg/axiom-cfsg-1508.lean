public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
  (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)

include F hr in
theorem sigmaMap_equiv {Q : (oppGraph G col w).ConnectedComponent} (φ : K ≃ compSet Q)
    (hφ : ∀ g i, (φ (g * s i) : {v : V // col v = false}) = r i (φ g)) (g : K) :
    sigmaMap G col w (φ g) = φ (τ g) := by
  have hex : ∃ (hx : (φ g : {v : V // col v = false}) ∈ oppSet G col w)
      (y : {v : V // col v = false}) (hy : y ∈ oppSet G col w),
      (oppGraph G col w).dist ⟨φ g, hx⟩ ⟨y, hy⟩ = 4 :=
    ⟨(φ g).2.1, φ (τ g), (φ (τ g)).2.1, by
      rw [dist_eq_of_equiv F hr φ hφ]
      exact (dist_eq_four_iff g (τ g)).mpr rfl⟩
  obtain ⟨hy, hd⟩ := sigmaMap_spec hex
  exact eq_of_dist_four F hr φ hφ g hy hd

end CFSG.Combinatorics.AperiodicOppositeComponents
end

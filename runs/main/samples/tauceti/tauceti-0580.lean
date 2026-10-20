public section

namespace TauCeti

attribute [instance] PlumbingGraph.decidableAdj

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] (P : PlumbingGraph V)

section Form

variable [Fintype V]

theorem intersectionForm_single_right (x : V → ℤ) (v : V) :
    P.intersectionForm x (Pi.single v 1) = ∑ i, x i * P.intersectionMatrix i v := by
  rw [intersectionForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single v
    (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun hv => absurd (Finset.mem_univ v) hv), Pi.single_eq_same, mul_one]

end Form
end PlumbingGraph
end TauCeti
end

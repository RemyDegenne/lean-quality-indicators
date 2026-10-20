public section

namespace TauCeti

open _root_.Quiver PathAlgebra

open scoped _root_.Matrix

universe u v w

section Graph

open DoubledQuiver

attribute [local instance] Fintype.ofFinite

variable {V : Type u} {G : SimpleGraph V}

variable (k : Type w) [Field k] [Fintype V] [DecidableRel G.Adj]

theorem AffineDynkinType.not_module_finite_preprojectiveAlgebra {t : AffineDynkinType}
    (ht : t.Valid) (hg : t.IsGraphical) (o : Orientation t.graph) :
    ¬ Module.Finite k (preprojectiveAlgebra k (OrientedQuiver t.graph o)) :=
  not_module_finite_preprojectiveAlgebra_orientedQuiver_of_two_mul_le_sum k o (δ := t.marks)
    (fun i => (AffineDynkinType.marks_pos i).le)
    (fun h => (AffineDynkinType.marks_pos (0 : Fin t.nodes)).ne' (congrFun h 0))
    (fun i => (AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg i).ge)

end Graph
end TauCeti
end

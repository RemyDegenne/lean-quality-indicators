namespace OAI

noncomputable section

open scoped Manifold ContDiff

open scoped Manifold ContDiff Topology

open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

open scoped Manifold ContDiff Topology

open Bundle Filter Set

open Set

open Bundle Set Filter

open scoped Topology

open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap

open scoped Topology

open scoped BigOperators

open scoped RealInnerProductSpace

namespace TamingCompatibility.UnitaryFrame

lemma fundamental_eval_line (v : V) : ⟪fundamental, line v⟫ = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [line, wedge, J, fundamental,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring

end TamingCompatibility.UnitaryFrame
end
end OAI

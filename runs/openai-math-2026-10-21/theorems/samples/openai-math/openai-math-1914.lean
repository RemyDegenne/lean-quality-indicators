namespace OAI

section

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert

open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set Filter

open scoped Manifold ContDiff RealInnerProductSpace Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma hodgeSmoothShift_cubes_commute (r s : ℝ) (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht r^3) ((hodgeSmoothShift A J α hs ht s^3) a) =
      (hodgeSmoothShift A J α hs ht s^3) ((hodgeSmoothShift A J α hs ht r^3) a) := by
  have h := ((hodgeSmoothShift_commute A J α hs ht r s).pow_pow 3 3).eq
  exact congrArg (fun L : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true => L a) h

end TamingCompatibility.GeometricHilbert
end
end
end
end
end OAI

public section

noncomputable section

open Bundle Filter Module Set

open scoped Topology

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] (ι : Type*)

namespace TauCeti

variable (F E) [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- An orientation of the real vector bundle `E` with model fibre `F`, indexed by `ι`: an
orientation of every fibre, such that near each point `b` the orientations of the fibres, read in
the preferred trivialization at `b`, all agree with that of the fibre over `b`. This is meaningful
when `ι` has cardinality the rank of the bundle; it is the condition that the fibre orientations
vary continuously with the base point. -/
structure VectorBundleOrientation where
  /-- The orientation of the fibre over each point. -/
  toFun : ∀ b, Orientation ℝ (E b) ι
  /-- The fibre orientations are locally constant in the preferred trivializations. -/
  eventually_mapOrientation_eq' : ∀ b, ∀ᶠ x in 𝓝 b,
    ∀ hx : x ∈ (trivializationAt F E b).baseSet,
      (trivializationAt F E b).mapOrientation ι hx (toFun x) =
        (trivializationAt F E b).mapOrientation ι (FiberBundle.mem_baseSet_trivializationAt' b)
          (toFun b)

end TauCeti
end
end

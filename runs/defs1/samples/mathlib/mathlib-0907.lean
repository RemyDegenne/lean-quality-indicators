@[expose] public section

open Bundle ContinuousLinearMap ENat Bornology

open scoped Manifold ContDiff Topology

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (IB n F E) in
/-- Consider a real vector bundle in which each fiber is endowed with a scalar product.
We say that the bundle is Riemannian if the scalar product depends smoothly on the base point.
This assumption is spelled `IsContMDiffRiemannianBundle IB n F E` where `IB` is the model space of
the base, `n` is the smoothness, `F` is the model fiber, and `E : B → Type*` is the bundle. -/
class IsContMDiffRiemannianBundle : Prop where
  exists_contMDiff : ∃ g : Π (x : B), E x →L[ℝ] E x →L[ℝ] ℝ,
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b))
    ∧ ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w

end
end

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace ContinuousMonoidHom

/-- The projection of a product `∀ i, A i` of topological monoids onto its `i`-th factor, as a
continuous homomorphism. This is the analogue for products of `ContinuousMonoidHom.fst` and
`ContinuousMonoidHom.snd`. -/
@[to_additive /-- The projection of a product `∀ i, A i` of topological additive monoids onto its
`i`-th factor, as a continuous additive homomorphism. This is the analogue for products of
`ContinuousAddMonoidHom.fst` and `ContinuousAddMonoidHom.snd`. -/]
def _root_.ContinuousMonoidHom.proj {ι : Type*} {A : ι → Type*} [∀ i, Monoid (A i)]
    [∀ i, TopologicalSpace (A i)] (i : ι) : (∀ i, A i) →ₜ* A i :=
  ⟨Pi.evalMonoidHom A i, continuous_apply i⟩

end ContinuousMonoidHom
end TauCeti
end

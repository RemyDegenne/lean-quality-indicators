public section

noncomputable section

namespace TauCeti.ContCohomology

variable (G : Type*) [Monoid G] [TopologicalSpace G]
  (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {ι : Type*} (H : ι → Type*) [∀ i, Monoid (H i)] [∀ i, TopologicalSpace (H i)]
  (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, IsTopologicalAddGroup (N i)] [∀ i, DistribMulAction (H i) (N i)]
  [∀ i, ContinuousSMul (H i) (N i)]

namespace SelmerStructure

variable {G M H N} (𝓕 : SelmerStructure G M H N)

/-- **The localisation map** `H¹(G, M) → H¹(H i, N i)` of a Selmer structure: pullback along the
compatible pair `(groupHom i, coeffHom i)`. -/
def localization (i : ι) : H1 G M →+ H1 (H i) (N i) :=
  explicitMap1 _ _ _ _ (𝓕.groupHom i) (𝓕.coeffHom i) (𝓕.continuous_coeffHom i) (𝓕.coeffHom_smul i)

end SelmerStructure
end TauCeti.ContCohomology
end
end

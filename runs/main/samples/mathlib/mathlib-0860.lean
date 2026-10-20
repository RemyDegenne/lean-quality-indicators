public section

open scoped Manifold

open Bundle Set Topology

section SpecificFunctions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']

variable {s : Set M} {x : M}

section Arithmetic

section Group

variable {z : M} {f g : M → E'} {f' g' : TangentSpace% z →L[𝕜] E'}

section sum

variable {ι : Type*} {t : Finset ι} {f : ι → M → E'} {f' : ι → TangentSpace% z →L[𝕜] E'}

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivAt.sum (hf : ∀ i ∈ t, HasMFDerivAt% (f i) z (f' i)) :
    HasMFDerivAt% (∑ i ∈ t, f i) z (∑ i ∈ t, f' i) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.sum hf

end sum
end Group
end Arithmetic
end SpecificFunctions
end

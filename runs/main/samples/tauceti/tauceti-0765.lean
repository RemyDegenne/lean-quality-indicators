public section

open Bundle Filter Topology

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module 𝕜 (V b)]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

theorem ContMDiffOn.smul_totalSpace {a : M → 𝕜} {g : M → TotalSpace F V} {s : Set M}
    (ha : ContMDiffOn J 𝓘(𝕜) n a s) (hg : ContMDiffOn J (I.prod 𝓘(𝕜, F)) n g s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F)) n
      (fun y => (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace F V)) s :=
  fun x hx => (ha x hx).smul_totalSpace (hg x hx)

end

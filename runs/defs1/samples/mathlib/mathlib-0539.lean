@[expose] public section

noncomputable section

open TopologicalSpace Opposite

open scoped ContDiff

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E H')
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (N G A A' R : Type u) [TopologicalSpace N] [ChartedSpace H N]
  [TopologicalSpace G] [ChartedSpace H G] [TopologicalSpace A] [ChartedSpace H A]
  [TopologicalSpace A'] [ChartedSpace H' A'] [TopologicalSpace R] [ChartedSpace H R]

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  (P : Type u) [TopologicalSpace P] [ChartedSpace HP P]

section ContMDiffRing

variable [Ring R] [ContMDiffRing I ∞ R]

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a presheaf
of rings. -/
def smoothPresheafRing : TopCat.Presheaf RingCat.{u} ↧M :=
  { obj := fun U ↦ ↧((smoothSheaf IM I M R).presheaf.obj U)
    map := fun h ↦ RingCat.ofHom <|
      ContMDiffMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

end ContMDiffRing
end
end

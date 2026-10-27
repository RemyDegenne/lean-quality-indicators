@[expose] public section

open scoped Manifold ContDiff

section ContMDiffMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H G] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

variable (I) (g h : G)

variable [ContMDiffMul I ∞ G]

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Used mostly through the notation `𝑹`.
Lemmas involving `smoothRightMul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨(· * g), contMDiff_mul_right⟩

end ContMDiffMul
end

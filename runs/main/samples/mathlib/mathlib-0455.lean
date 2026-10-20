public section

open scoped Topology Manifold

open Function Set Bundle ChartedSpace

section DerivativesProperties

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f f₁ : M → M'} {x : M} {s t : Set M} {g : M' → M''} {u : Set M'}

variable {I}

variable {n : WithTop ℕ∞}

variable {f' f₀' f₁' : TangentSpace% x →L[𝕜] TangentSpace% (f x)}
  {g' : TangentSpace% (f x) →L[𝕜] TangentSpace% (g (f x))}

theorem HasMFDerivWithinAt.congr_mfderiv (h : HasMFDerivAt[s] f x f') (h' : f' = f₁') :
    HasMFDerivAt[s] f x f₁' :=
  h' ▸ h

end DerivativesProperties
end

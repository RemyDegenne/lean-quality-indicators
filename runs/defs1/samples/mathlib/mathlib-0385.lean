@[expose] public section

noncomputable section

open scoped Manifold ContDiff

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  {n : ℕ∞ω}

namespace ContMDiffMap

section GroupStructure

variable (I N)

variable (I') {N}

/-- For a Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction' group homomorphism from
`C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/
@[to_additive /-- For an additive Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction'
group homomorphism from `C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/]
def restrictMonoidHom (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] {U V : Opens N} (h : U ≤ V) : C^n⟮I, V; I', G⟯ →* C^n⟮I, U; I', G⟯ where
  toFun f := ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end GroupStructure
end ContMDiffMap
end
end

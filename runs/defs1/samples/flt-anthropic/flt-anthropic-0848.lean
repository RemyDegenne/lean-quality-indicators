namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt

attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped Classical

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace P2mAdjoinChart

section Chains

variable {V : Scheme.{u}} (K K' : V.OrderedAffineCover) (e : K.ι ↪o K'.ι) (j₀ : K'.ι)
  (hj₀ : ∀ j : K'.ι, j = j₀ ∨ j ∈ Set.range e) (hlt : ∀ i, e i < j₀)

def vtx : K'.Idx 0 := ⟨fun _ => j₀, fun a b h => absurd h (by rw [fin_one_eq a b]; exact lt_irrefl _)⟩

end Chains
end P2mAdjoinChart
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt

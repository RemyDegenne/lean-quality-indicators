public section

namespace TauCeti

open Filter

open scoped RestrictedProduct

universe u v w

variable {ι : Type u} {G : ι → Type v}

variable [∀ i, Group (G i)]

@[to_additive continuous_addRestrictedProductCongrRight]
theorem continuous_restrictedProductCongrRight {H : ι → Type w} [∀ i, Group (H i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, TopologicalSpace (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (hcont : ∀ i, Continuous (φ i)) :
    Continuous (restrictedProductCongrRight U U' φ hφ) := by
  convert continuous_restrictedProductMap U U' (fun i ↦ (φ i).toMonoidHom)
    (hφ.mono fun _ hi ↦ hi.mapsTo) hcont using 1
  ext x i
  simp

end TauCeti
end

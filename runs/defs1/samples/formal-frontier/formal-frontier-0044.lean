@[expose] public section

universe u v w w₁

namespace Subcoalgebra

variable {K : Type u} {C : Type v} {C' : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

/-- A coalgebra homomorphism injective on a subcoalgebra gives a coalgebra equivalence
from that subcoalgebra to its image. Ambient injectivity is not required. -/
noncomputable def equivMapOfInjOn (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) : D ≃ₗc[K] map f D := by
  let g : D →ₗc[K] map f D :=
    (f.comp D.subtype).codRestrict (map f D)
      (fun x ↦ mem_map.mpr ⟨(x : C), x.property, rfl⟩)
  refine CoalgEquiv.ofBijective (f := g) ⟨?_, ?_⟩
  · exact LinearMap.submoduleMap_injective_of_injOn
      (f := f.toLinearMap) (p := D.toSubmodule) hf
  · intro y
    obtain ⟨x, hx, hxy⟩ := mem_map.mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end Subcoalgebra
end

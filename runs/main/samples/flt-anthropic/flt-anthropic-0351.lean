set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Galois

variable {K k : Type*} [Field K] [Field k]

omit [Field K] in

theorem specializePlace_intertwines (r : K → k) (σ : K → K) (τ : k → k)
    (h : ∀ a, r (σ a) = τ (r a)) (a : K) :
    specializePlace r (σ a) = charLGeomPlaceOfPoint k (τ (r a)) := by
  simp only [specializePlace, h]

end Galois
end ModularCurve
end

@[expose] public section

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

open TauCeti.DavisKahan.ExactSinTheta

universe u v

section ScalarGeneric

variable {𝕜 : Type u} [RCLike 𝕜]

variable {H F G : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Package a bounded perturbation and two invariant block embeddings as the
paper-shaped unbounded residual data.  The residual identity is automatic and
has residual `V ∘ X`. -/
noncomputable def boundedPerturbationSinThetaData
    (A : H →ₗ.[𝕜] H) (V : H →L[𝕜] H)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (X : F →L[𝕜] H) (F₁ : G →L[𝕜] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A V) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y)) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := H) (F := F) (G := G) where
  A := TauCeti.LinearPMap.addBounded A V
  A₀ := A₀
  Λ₁ := Λ₁
  X := X
  F₁ := F₁
  residual := V ∘L X
  X_maps_domain := hXdom
  F₁_maps_domain := hF₁dom
  residual_eq := by
    intro x
    change
      (A ⟨X (x : F), hXdom x⟩ + V (X (x : F))) -
          X (A₀ x) =
        V (X (x : F))
    rw [hXintertwines x]
    abel
  intertwines := hF₁intertwines

end ScalarGeneric
end DavisKahan
end TauCeti
end

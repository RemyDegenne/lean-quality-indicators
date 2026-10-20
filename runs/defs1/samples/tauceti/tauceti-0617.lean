public section

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The cup form** of a linear functional `φ : H²(G, 𝔽_p) →ₗ 𝔽_p`: the `𝔽_p`-bilinear form
`(a, b) ↦ φ (a ⌣ b)` on `H¹(G, 𝔽_p)`. For a Demushkin group, where `H²(G, 𝔽_p)` is
one-dimensional, an isomorphism `φ : H²(G, 𝔽_p) ≅ 𝔽_p` turns the cup square into the
nondegenerate bilinear form of Labute's definition. -/
noncomputable def _root_.LinearMap.cupForm (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p) :
    LinearMap.BilinForm (ZMod p) (cohomFp p G 1) :=
  (cupFp p G).compr₂ φ

end TauCeti
end

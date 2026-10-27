public section

open MeasureTheory Set

open scoped ENNReal

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- `z ∈ L²(I; H^m(U))`, with derivative family `D`: each `D α` with
`α.length ≤ m` is square integrable on `U × I`, `D []` is `z` almost
everywhere on `U × I`, and `D (α ++ [j])` is the distributional `j`-th spatial
derivative of `D α` on `U × I`. A field in `L²(U × I)` whose spatial
distributional derivatives through order `m` are in `L²(U × I)` is exactly an
element of `L²(I; H^m(U))`. -/
structure IsL2SobolevFamilyOn (m : ℕ) (U : Set Vec3) (I : Set ℝ) (z : Vec3 × ℝ → ℝ)
    (D : List (Fin 3) → Vec3 × ℝ → ℝ) : Prop where
  memL2 : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 (volume.restrict (U ×ˢ I))
  zero : D [] =ᵐ[volume.restrict (U ×ˢ I)] z
  weak : ∀ (α : List (Fin 3)) (j : Fin 3), α.length < m →
    ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U ×ˢ I →
      ∫ p in U ×ˢ I, D α p * spatialPartial φ j p =
        -∫ p in U ×ˢ I, D (α ++ [j]) p * φ p

end CKN
end
end

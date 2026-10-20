public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

theorem galoisF2Iso_hom_cup (m n : ℕ)
    (x : continuousCohomology m (trivialF2 ↥(galoisSubgroup K L σ).toSubgroup))
    (y : continuousCohomology n (trivialF2 ↥(galoisSubgroup K L σ).toSubgroup)) :
    (galoisF2Iso K L σ (m + n)).hom
        ((trivialF2TopPairing (galoisSubgroup K L σ).toSubgroup).cup m n x y) =
      (trivialF2TopPairing (AbsoluteGaloisGroup L)).cup m n
        ((galoisF2Iso K L σ m).hom x) ((galoisF2Iso K L σ n).hom y) := by
  simp only [galoisF2Iso_hom, trivialF2Map_cup]

end TauCeti
end
end

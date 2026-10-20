public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w

namespace TopCat

variable {k : Type w} [CommRing k]

section Unit

variable (k) [NoZeroDivisors k] [IsPrincipalIdealRing k] (X Y : TopCat.{w})

/-- **The Künneth short exact sequence over a principal ideal domain splits**, so that
`Hₘ₊₁(X × Y; k)` is the direct sum of `⨁_{p + q = m + 1} Hₚ(X; k) ⊗ H_q(Y; k)` and
`⨁_{p + q = m} Tor₁(Hₚ(X; k), H_q(Y; k))`
(`CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct`).
The splitting depends on chosen splittings of the cycles of the singular chain complexes, and need
not be natural in `X` and `Y`. -/
def singularHomologyKunnethUnitSplitting (m : ℕ) :
    (singularHomologyKunnethUnitShortComplex k X Y m).Splitting :=
  have : Module.Projective k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Projective k k)
  have := isSplitMono_singularHomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ _) (m + 1)
  -- a retraction of the Künneth map, preceded by the map induced by the inverse unitor
  .ofExactOfRetraction _ (singularHomologyKunnethUnitShortComplex_shortExact k X Y m).exact
    (((singularHomologyFunctor _ (m + 1)).map (λ_ (𝟙_ (ModuleCat.{w} k))).inv).app (X ⊗ Y) ≫
      retraction (singularHomologyKunneth X Y (𝟙_ _) (𝟙_ _) (m + 1)))
    (by simp) (singularHomologyKunnethUnitShortComplex_shortExact k X Y m).epi_g

end Unit
end TopCat
end
end

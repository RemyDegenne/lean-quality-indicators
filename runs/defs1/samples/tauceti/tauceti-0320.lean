public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

universe u

variable {R : Type u} [CommRing R]

section Kunneth

variable (K L : ChainComplex (ModuleCat.{u} R) ℕ)

variable [∀ q, Projective (cokernel (L.iCycles q))]

variable [∀ q, Projective (L.cycles q)]

variable [∀ p, IsSplitMono (K.iCycles p)]

/-- **The Künneth short exact sequence splits** when, in addition, the cycles of `K` split off its
terms; for instance for complexes `K` and `L` of projective modules over a principal ideal domain.
The splitting comes from a retraction of the Künneth map
(`HomologicalComplex.isSplitMono_homologyKunneth`) built from chosen splittings of the cycles, so
it need not be natural in `K` and `L`. -/
def homologyKunnethShortComplexSplitting (m : ℕ) : (homologyKunnethShortComplex K L m).Splitting :=
  have := isSplitMono_homologyKunneth K L (m + 1)
  .ofExactOfRetraction _ (homologyKunnethShortComplex_shortExact K L m).exact
    (retraction (homologyKunneth K L (m + 1))) (IsSplitMono.id _)
    (homologyKunnethShortComplex_shortExact K L m).epi_g

end Kunneth
end HomologicalComplex
end
end

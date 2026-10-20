public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

section Split

variable {k : Type w} [CommRing k]

section

variable (X Y : TopCat.{w}) (M N : ModuleCat.{w} k)
  [∀ p, IsSplitMono (((toSSet.obj X).chainComplex M).iCycles p)]
  [∀ p, IsSplitEpi (((toSSet.obj X).chainComplex M).homologyπ p)]
  [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex N).iCycles q)]
  [∀ q, IsSplitEpi (((toSSet.obj Y).chainComplex N).homologyπ q)]

/-- **The Künneth isomorphism** `⨁_{p + q = n} Hₚ(X; M) ⊗ H_q(Y; N) ≅ Hₙ(X × Y; M ⊗ N)`, induced
by the homology cross product, when the cycles of the singular chain complexes split off their
terms and their homology splits off their cycles; for instance for semisimple modules `M` and `N`
over a commutative ring, such as any modules over a field. -/
def singularHomologyKunnethIso (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ ((singularHomologyFunctor _ p).obj M).obj X)
        (fun q ↦ ((singularHomologyFunctor _ q).obj N).obj Y) n ≅
      ((singularHomologyFunctor _ n).obj (M ⊗ N)).obj (X ⊗ Y) :=
  asIso (singularHomologyKunneth X Y M N n)

end
end Split
end TopCat
end
end

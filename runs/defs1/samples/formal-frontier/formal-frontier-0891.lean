@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

/-- The ordinary-space homology map obtained naturally from the two-open
short complexes.  It is defined by conjugating the cover-small map by the
canonical cover-small/ordinary homology isomorphisms. -/
noncomputable def twoOpenMayerVietorisSpaceMap {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) :
    integralSingularHomology X n ⟶ integralSingularHomology Y n :=
  (twoOpenSpaceHomologyIso U V hUV n).inv ≫
    HomologicalComplex.homologyMap
      (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₃ n ≫
    (twoOpenSpaceHomologyIso U' V' hU'V' n).hom

end AlgebraicTopology
end
end

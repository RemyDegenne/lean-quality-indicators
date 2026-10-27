set_option warningAsError true

@[expose] public section

universe u v

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- In one common small universe, continuous cohomology commutes with raising
the acting group and coefficient carrier. -/
noncomputable def continuousCohomologyUliftIsoSameUniverse
    (X : TopRep.{v} k G) (n : ℕ) :
    (TopModuleCat.uliftFunctor.{v, v} k).obj (continuousCohomology n X) ≅
      continuousCohomology n (TopRep.ulift.{u, v, v, v, v} X) :=
  ((X.homogeneousCochains.sc n).mapHomologyIso
      (TopModuleCat.uliftFunctor.{v, v} k)).symm ≪≫
    HomologicalComplex.homologyMapIso
      (homogeneousCochainsUliftIsoSameUniverse X) n

end TopRep
end

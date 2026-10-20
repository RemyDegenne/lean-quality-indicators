set_option warningAsError true

@[expose] public section

universe u v w v' w'

open CategoryTheory ContinuousMap

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma resolutionUliftIsoSameUniverse_d_comm
    (X : TopRep.{v} k G) (n : ℕ) :
    TopRep.uliftMap.{u, v, v, v, v} (TopRep.d X n) ≫
        (resolutionUliftIsoSameUniverse X (n + 1)).hom =
      (resolutionUliftIsoSameUniverse X n).hom ≫
        TopRep.d (TopRep.ulift.{u, v, v, v, v} X) n := by
  induction n with
  | zero =>
      ext x g
      rfl
  | succ n ih =>
      have ih' := ih
      simp only [resolutionUliftIsoSameUniverse, Iso.trans_hom,
        Functor.mapIso_hom] at ih'
      rw [TopRep.d_succ, TopRep.d_succ, uliftMap_sub]
      rw [Preadditive.sub_comp, Preadditive.comp_sub]
      simp only [resolutionUliftIsoSameUniverse,
        Iso.trans_hom, Functor.mapIso_hom]
      congr 1
      rw [← Category.assoc, uliftMap_coind₁Map_comp_coind₁UliftIso]
      rw [Category.assoc, coind₁Map_comp, ih', ← coind₁Map_comp,
        ← Category.assoc]

end TopRep
end

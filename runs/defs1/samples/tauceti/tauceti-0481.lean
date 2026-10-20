public section

noncomputable section

open Set TauCeti.SetLike

namespace PreAbstractSimplicialComplex

open AbstractSimplicialComplex

variable {α β : Type*} [DecidableEq β]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}

variable (P : PreAbstractSimplicialComplex α) (f : α ↪ β)
  (hK : P ≤ K.toPreAbstractSimplicialComplex)
  (hL : P.map f ≤ L.toPreAbstractSimplicialComplex)

/-- An injective relabeling carrying the underlying precomplex of `K` onto `R` identifies the
realization of `K` with the polyhedron of `R`, inside any ambient weak realization containing
`R`. -/
def realizationRelabelingHomeomorph {R : PreAbstractSimplicialComplex β}
    (hmap : P.map f = R) (hP : P = K.toPreAbstractSimplicialComplex)
    (hR : R ≤ L.toPreAbstractSimplicialComplex) :
    Realization K ≃ₜ {y : Realization L // y.1.support ∈ R} :=
  ((Homeomorph.Set.univ _).symm.trans
    (Homeomorph.setCongr (s := Set.univ) (t := {x : Realization K | x.1.support ∈ P})
      (Set.eq_univ_of_forall fun x => by
        rw [hP]
        exact AbstractSimplicialComplex.support_mem _ x).symm)).trans
    ((P.relabelingHomeomorph f hP.le (by rw [hmap]; exact hR)).trans
      (Homeomorph.setCongr (s := {x : Realization L | x.1.support ∈ P.map f})
        (t := {x : Realization L | x.1.support ∈ R}) (by rw [hmap])))

end PreAbstractSimplicialComplex
end
end

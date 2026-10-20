@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

local instance : Limits.PreservesFiniteLimits (lftPoints K) :=
  lftPointsPreservesFiniteLimits K

local instance : CartesianMonoidalCategory
    (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) :=
  .ofHasFiniteProducts

local instance : (lftPoints K).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- A pointwise subgroup of the functor of points of a group scheme induces a
group-object structure on its representing locally-finite-type scheme. The
finite-type subscheme case follows Milne, *Algebraic Groups* (2017), item 1.5;
the reflection uses full faithfulness from `SchemeProperties.FiniteTypePoints`. -/
abbrev pointwiseSubgroupGrpObj
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) : GrpObj X := by
  letI : GrpObj ((lftPoints K).obj X) := h.grpObj
  exact (lftPointsFullyFaithful K).grpObj X

end AlgebraicGeometry
end
end

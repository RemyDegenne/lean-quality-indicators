public section

set_option warningAsError true

open CategoryTheory Limits Opposite Set Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

variable {K : Type u} [Field K]

local instance componentFibersGlobalSectionsAlgebra
    {F : Type u} [Field F] (X : Over (Spec (.of F))) :
    Algebra F Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra F

theorem componentSubalgebra_fiber_eq_bot
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    letI : Algebra ((componentScheme X).left.residueField x)
        Γ((toComponentScheme X).left.fiber x, ⊤) :=
      ((toComponentScheme X).left.fiberToSpecResidueField x).globalSectionsAlgebra _
    @componentSubalgebra ((componentScheme X).left.residueField x) _
        (componentSchemeFiber X x)
        (fiberToComponentSchemeLocallyOfFiniteType X x)
        (fiberToComponentSchemeQuasiCompact X x) =
      (⊥ : Subalgebra ((componentScheme X).left.residueField x)
        Γ((toComponentScheme X).left.fiber x, ⊤)) := by
  let _ : LocallyOfFiniteType (componentSchemeFiber X x).hom :=
    fiberToComponentSchemeLocallyOfFiniteType X x
  let _ : QuasiCompact (componentSchemeFiber X x).hom :=
    fiberToComponentSchemeQuasiCompact X x
  let _ : Algebra ((componentScheme X).left.residueField x)
      Γ((componentSchemeFiber X x).left, ⊤) :=
    (componentSchemeFiber X x).hom.globalSectionsAlgebra _
  let _ : GeometricallyConnected (componentSchemeFiber X x).hom :=
    geometricallyConnected_fiber_toComponentScheme X x
  let _ : Algebra
      (IsLocalRing.ResidueField ((componentScheme X).left.presheaf.stalk x))
      (SeparableClosure ((componentScheme X).left.residueField x)) := by
    change Algebra ((componentScheme X).left.residueField x)
      (SeparableClosure ((componentScheme X).left.residueField x))
    infer_instance
  let _ : ConnectedSpace
      (schemeBaseChange (componentSchemeFiber X x)
        (L := SeparableClosure ((componentScheme X).left.residueField x))).left := by
    exact GeometricallyConnected.geometrically_connectedSpace
      (f := (componentSchemeFiber X x).hom) _ _ _
      (IsPullback.of_hasPullback _ _)
  have hcard : Nat.card (ConnectedComponents
      (schemeBaseChange (componentSchemeFiber X x)
        (L := SeparableClosure ((componentScheme X).left.residueField x))).left) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  apply Subalgebra.eq_bot_of_finrank_one
  rw [componentSubalgebra_finrank_eq_natCard_separableClosure
    (k := ((componentScheme X).left.residueField x))
    (componentSchemeFiber X x)]
  exact hcard

end
end AlgebraicGeometry
end

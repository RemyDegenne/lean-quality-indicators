public section

noncomputable section

namespace AbstractSimplicialComplex

open PreAbstractSimplicialComplex.SimplicialMap

variable {α : Type*} [LinearOrder α] (K : AbstractSimplicialComplex α)
  (hK : K.faces.Finite)

@[simp]
theorem orderedCylinderRealizationHomeomorph_fst_val (z : Realization K.orderedCylinder) :
    (K.orderedCylinderRealizationHomeomorph hK z).1.1 = Finsupp.mapDomain Prod.fst z.1 := by
  -- Eliminate the carrier equality before applying the product computation rule.
  unfold orderedCylinderRealizationHomeomorph
  generalize_proofs hfin hEq
  generalize K.orderedCylinder = C at hEq z ⊢
  cases hEq
  let z' : Realization (K.orderedProd (⊤ : AbstractSimplicialComplex (Fin 2))) := z
  have h := K.orderedProdRealizationMap_fst_val (⊤ : AbstractSimplicialComplex (Fin 2)) z'
  rw [← orderedProdRealizationHomeomorph_apply K _
    (finite_faces_orderedProd hK (Set.toFinite _))] at h
  exact h

end AbstractSimplicialComplex
end
end

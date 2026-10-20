public section

namespace TauCeti

open _root_.IntermediateField MulAction Polynomial

open scoped Pointwise

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

variable [Normal F E]

/-- For a root whose point stabilizer fixes `F⟮x⟯`, conjugates of the simple field correspond
to conjugates of that stabilizer in the polynomial Galois group. Such a root exists by
`exists_root_map_stabilizer_eq_fixingSubgroup`. -/
noncomputable def conjugateSimpleFieldsEquivConjugateSubgroups (x : E)
    (hsep : (minpoly F x).Separable)
    (y : (minpoly F x).rootSet (minpoly F x).SplittingField)
    (hy : (stabilizer (minpoly F x).Gal y).map
      (galEquivNormalClosure (F := F) (E := E) x).toMonoidHom =
        (F⟮x⟯.restrict (le_normalClosure F⟮x⟯)).fixingSubgroup) :
    conjugateSimpleFields (F := F) x ≃
      MulAction.orbit (ConjAct (minpoly F x).Gal) (stabilizer (minpoly F x).Gal y) := by
  let _ : FiniteDimensional F (normalClosure F F⟮x⟯ E) :=
    finiteDimensional_normalClosure_adjoin_simple (Algebra.IsIntegral.isIntegral x)
  let _ : IsGalois F (normalClosure F F⟮x⟯ E) :=
    isGalois_normalClosure_adjoin_simple x hsep
  let e := MulEquiv.conjugateSubgroupsEquiv (galEquivNormalClosure (F := F) (E := E) x)
    (stabilizer (minpoly F x).Gal y)
  have he : MulAction.orbit (ConjAct (minpoly F x).Gal) (stabilizer (minpoly F x).Gal y) ≃
      MulAction.orbit (ConjAct Gal(normalClosure F F⟮x⟯ E/F))
        (F⟮x⟯.restrict (le_normalClosure F⟮x⟯)).fixingSubgroup :=
    e.trans (Equiv.subtypeEquivRight fun J ↦ by
      rw [← hy, MulEquiv.toMonoidHom_eq_coe])
  exact (IntermediateField.conjugateFieldsEquivConjugateSubgroups
    (F⟮x⟯.restrict (le_normalClosure F⟮x⟯))).trans he.symm

end TauCeti
end

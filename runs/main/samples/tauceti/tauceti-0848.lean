public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

theorem isSl2Triple_rep_serreRootGenerator (i : Fin 4) :
    _root_.IsSl2Triple
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreH ℚ CartanMatrix.F₄ᵀ i)))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator CartanMatrix.F₄ᵀ (.inl i))))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator CartanMatrix.F₄ᵀ (.inr i)))) := by
  have hne : Matrix.toLinAlgEquiv' (R := ℚ) (n := Fin 26) (cartanMatrixRat i) ≠ 0 := fun hz ↦
    (isSl2TripleRat i).h_ne_zero
      ((Matrix.toLinAlgEquiv' (R := ℚ) (n := Fin 26)).injective (hz.trans (map_zero _).symm))
  have h := (isSl2TripleRat i).map
    (Matrix.toLinAlgEquiv' (R := ℚ) (n := Fin 26)).toAlgHom.toLieHom hne
  simp only [AlgHom.toLieHom_apply, AlgEquiv.toAlgHom_apply] at h
  rw [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr]
  simpa only [rep_ι, rationalSerreRepresentation_serreH, rationalSerreRepresentation_serreE,
    rationalSerreRepresentation_serreF] using h

end TauCeti.F4ShortRoot
end

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization

open CFSG.Wreathed.CentralSL2 CFSG.ComponentClassification.CatalogueSchreierLinearTwo

open scoped Pointwise

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem conj_modelY {h : SemilinearExtension F b m hm heven Sigma hSigma} {G : GL (Fin 2) F}
    (hG : projectiveMap F b m hm heven h.left = ProjGenLinGroup.mk G) :
    h * modelY b m hm heven Sigma hSigma * h⁻¹ =
      SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
        specialInclusion F b m hm heven (matrixConjugation F G (weyl F))) := by
  rw [modelY_eq, semidirect_conj_inl, fieldAction_involutionY, conj_involutionY hG]

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
end

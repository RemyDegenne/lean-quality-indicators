public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization

open CFSG.Wreathed.CentralSL2 CFSG.ComponentClassification.CatalogueSchreierLinearTwo

open scoped Pointwise

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem mem_rootGroup_iff {i : F} {hi : i * i = -1}
    {x : SemilinearExtension F b m hm heven Sigma hSigma} :
    x ∈ rootGroup b m hm heven Sigma hSigma i hi ↔
      ∃ l, SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi l)) = x := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.toAdd, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨Multiplicative.ofAdd l, rfl⟩

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
end

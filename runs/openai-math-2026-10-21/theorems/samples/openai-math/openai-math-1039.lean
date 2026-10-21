namespace OAI

noncomputable section

namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

theorem predual_ext (F G : StrongDual ℂ (ConcretePredual M))
    (h : ∀ x y, F (predualCoefficient M x y) = G (predualCoefficient M x y)) : F = G := by
  obtain ⟨f, hf, _⟩ := exists_extension_norm_eq (normalFunctionalSpace M).toSubmodule F
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq (normalFunctionalSpace M).toSubmodule G
  have hspan : Submodule.span ℂ (Set.range fun xy : H × H => normalCoefficient M xy.1 xy.2) ≤
      (f - g).ker := by
    apply Submodule.span_le.mpr
    rintro φ ⟨⟨x, y⟩, rfl⟩
    change f (normalCoefficient M x y) - g (normalCoefficient M x y) = 0
    exact sub_eq_zero.mpr ((hf (predualCoefficient M x y)).trans
      ((h x y).trans (hg (predualCoefficient M x y)).symm))
  have hc := closure_minimal hspan (f - g).isClosed_ker
  apply ContinuousLinearMap.ext
  intro φ
  have hz := hc φ.property
  change f (φ : StrongDual ℂ M.toStarSubalgebra) -
    g (φ : StrongDual ℂ M.toStarSubalgebra) = 0 at hz
  exact (hf φ).symm.trans ((sub_eq_zero.mp hz).trans (hg φ))

end KadisonSimilarity
end
end OAI

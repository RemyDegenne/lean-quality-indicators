namespace OAI

noncomputable section

namespace KadisonSimilarity

open scoped TensorProduct

variable {G H K L : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

@[simp] theorem inner_hilbertTensorInsert (a b : G) (x y : H) :
    inner ℂ (hilbertTensorInsert a x) (hilbertTensorInsert b y) =
      inner ℂ a b * inner ℂ x y := by
  exact (UniformSpace.Completion.inner_coe (a ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] y)).trans
    (TensorProduct.inner_tmul ℂ a b x y)

end KadisonSimilarity
end
end OAI

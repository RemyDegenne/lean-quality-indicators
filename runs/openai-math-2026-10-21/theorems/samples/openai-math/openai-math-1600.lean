namespace OAI

noncomputable section

namespace PolycyclicRecognition

open scoped TensorProduct

variable {K M V : Type} [Field K] [AddCommGroup M] [Module ℤ M]
  [AddCommGroup V] [Module K V]

theorem tensorMultilinear_ext {n : ℕ}
    (F G : MultilinearMap K (fun _ : Fin n => K ⊗[ℤ] M) V)
    (h : ∀ a : Fin n → M,
      F (fun i => scalarTensorUnit K M (a i)) =
        G (fun i => scalarTensorUnit K M (a i))) : F = G := by
  ext v
  apply sub_eq_zero.mp
  apply tensorMultilinear_zero_on_generators (F - G) Finset.univ v
  intro a
  simpa only [Finset.mem_univ, ↓reduceIte, sub_apply, sub_eq_zero] using h a

end PolycyclicRecognition
end
end OAI

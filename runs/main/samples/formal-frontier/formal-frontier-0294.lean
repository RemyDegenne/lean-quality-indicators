@[expose] public section

open scoped DirectSum TensorProduct

universe u v w

namespace Module.FaithfullyFlat

theorem directSum_iff
    (R : Type u) {ι : Type v} (M : ι → Type w)
    [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Module.FaithfullyFlat R (⨁ i, M i) ↔
      (∀ i, Module.Flat R (M i)) ∧
        ∀ I : Ideal R, I ≠ ⊤ → ∃ i, Nontrivial ((R ⧸ I) ⊗[R] M i) := by
  classical
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal, Module.Flat.directSum_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun I ↦ imp_congr_right fun _ ↦ ?_
  exact Submodule.Quotient.nontrivial_iff.symm.trans <|
    (TensorProduct.quotTensorEquivQuotSMul (⨁ i, M i) I).toEquiv.nontrivial_congr.symm.trans <|
    (TensorProduct.directSumRight R R (R ⧸ I) M).toEquiv.nontrivial_congr.trans <|
    nontrivial_directSum_iff _

end Module.FaithfullyFlat
end

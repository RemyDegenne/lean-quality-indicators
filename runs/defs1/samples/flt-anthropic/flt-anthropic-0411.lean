namespace P2MW.S_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel TensorProduct

open scoped TensorProduct.RightActions NNReal ENNReal Pointwise

noncomputable section

namespace AutomorphicForm

namespace BaseChangeUnitSectionFn

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section Embedding

def pairGL : Garch L × Gfin L →* Gad L where
  toFun x :=
    { val := pairMat (x.1 : Matrix (Fin 2) (Fin 2) _) (x.2 : Matrix (Fin 2) (Fin 2) _)
      inv := pairMat ((x.1⁻¹ : Garch L) : Matrix (Fin 2) (Fin 2) _) ((x.2⁻¹ : Gfin L) : Matrix (Fin 2) (Fin 2) _)
      val_inv := by rw [← pairMat_mul]; simp only [Units.mul_inv]; exact pairMat_one
      inv_val := by rw [← pairMat_mul]; simp only [Units.inv_mul]; exact pairMat_one }
  map_one' := Units.ext (by simp only [Units.val_one, Prod.fst_one, Prod.snd_one]; exact pairMat_one)
  map_mul' x y := Units.ext (by
    simp only [Units.val_mul, Prod.fst_mul, Prod.snd_mul]
    exact pairMat_mul _ _ _ _)

end Embedding
end BaseChangeUnitSectionFn
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange

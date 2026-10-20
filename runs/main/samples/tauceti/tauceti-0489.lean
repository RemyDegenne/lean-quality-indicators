public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L A : Type*} [Field k] [Field L] [Algebra k L]

variable [AddCommGroup A] [Module k A] [IsGalois k L]

theorem tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq (x : L ⊗[k] A) :
    (∀ σ : L ≃ₐ[k] L, TensorProduct.map σ.toLinearMap LinearMap.id x = x) ↔
      ∃ a : A, 1 ⊗ₜ[k] a = x := by
  classical
  let b := Module.Free.chooseBasis k A
  constructor
  · intro hx
    have hc (i) : ∃ c : k, algebraMap k L c = (b.baseChange L).repr x i := by
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      exact (b.map_baseChange_repr σ.toLinearMap x i).trans
        (congrArg (fun y ↦ (b.baseChange L).repr y i) (hx σ))
    choose c hc using hc
    refine ⟨∑ i ∈ ((b.baseChange L).repr x).support, c i • b i, ?_⟩
    conv_rhs => rw [← (b.baseChange L).linearCombination_repr x]
    simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      Finsupp.linearCombination_apply, Finsupp.sum, Module.Basis.baseChange_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hc i]
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']
  · rintro ⟨a, rfl⟩ σ
    simp

end TauCeti.GaloisDescent
end

namespace OAI

section

namespace ElementaryPositivity.RawShuffle

open scoped TensorProduct

open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma restrictionBUnit_unitalSourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (A : Cut d e) (W : ℤ) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) :
    restrictionBUnit a c η hc hs A f∈unitalSourceTensorFiltration a c η hc θ d e W := by
  by_cases hd : d=0
  · subst d
    have hr : restrictionBUnit a c η hc hs A f=(1 : B a (slope c η) 0)⊗ₜ[ℚ]castB a _ (zero_add e) f := by
      simpa only [castB_trans,castB_rfl] using restrictionBUnit_zero_left a c η hc A (castB a _ (zero_add e) f)
    rw [hr]
    exact tmul_mem_additiveTensorFiltration _ _ (by omega)
      (unitalSourceFiltration_unit a c η hc θ)
      (castB_mem_unitalSourceFiltration a c η hc θ (zero_add e) W hf)
  by_cases he : e=0
  · subst e
    have hr : restrictionBUnit a c η hc hs A f=castB a _ (add_zero d) f⊗ₜ[ℚ](1 : B a (slope c η) 0) := by
      simpa only [castB_trans,castB_rfl] using restrictionBUnit_zero_right a c η hc A (castB a _ (add_zero d) f)
    rw [hr]
    exact tmul_mem_additiveTensorFiltration _ _ (by omega)
      (castB_mem_unitalSourceFiltration a c η hc θ (add_zero d) W hf)
      (unitalSourceFiltration_unit a c η hc θ)
  have hde : d+e≠0 := add_ne_zero_left _ _ hd
  have hs' : slope c η d=slope c η e := hs.resolve_left hd |>.resolve_left he
  rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) hde W] at hf
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he W,
    restrictionBUnit_independent a c η hc hs A (firstCut d e),
    show restrictionBUnit a c η hc hs (firstCut d e)=restrictionB a c η hc hs' (firstCut d e) from rfl]
  exact restrictionB_sourceTensorFiltration a c η hc θ d e hs' W f hf

end ElementaryPositivity.RawShuffle
end
end OAI

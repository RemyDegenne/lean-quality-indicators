@[expose] public section

universe u v w z

namespace IsCoveringMap

section Extension

variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  {p : E → B} {q : F → B} (covp : IsCoveringMap p) (covq : IsCoveringMap q)
  {b : B}

theorem fiberMapEquivOfPathConnected_symm_eq_iff
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (h : @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul)
    (f : {f : C(E, F) // q ∘ f = p}) :
    (covp.fiberMapEquivOfPathConnected covq e₀).symm h = f ↔ f.val e₀ = (h ⟨e₀, rfl⟩).val := by
  constructor
  · rintro rfl
    exact covp.fiberMapEquivOfPathConnected_symm_apply_coe covq e₀ h ⟨e₀, rfl⟩
  · intro hf
    apply Subtype.ext
    apply DFunLike.ext'
    exact covq.eq_of_comp_eq ((covp.fiberMapEquivOfPathConnected covq e₀).symm h).val.continuous
      f.val.continuous
      (((covp.fiberMapEquivOfPathConnected covq e₀).symm h).property.trans f.property.symm) e₀
      ((covp.fiberMapEquivOfPathConnected_symm_apply_coe covq e₀ h ⟨e₀, rfl⟩).trans hf.symm)

end Extension
end IsCoveringMap
end

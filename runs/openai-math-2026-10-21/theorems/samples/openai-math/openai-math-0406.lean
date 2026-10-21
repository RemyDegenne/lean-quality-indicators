namespace OAI

section

namespace ElementaryPositivity.RawShuffle

variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] Classical.propDecidable

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)

noncomputable local instance : AddCommGroup (primitiveSpace a c η hc θ hχ d W) := Submodule.addCommGroup _

noncomputable local instance : Module ℚ (primitiveSpace a c η hc θ hχ d W) := Submodule.module _

noncomputable local instance : AddCommGroup (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.addCommGroup _

noncomputable local instance : Module ℚ (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.module _

lemma stringBaseComponent_twice (ℓ m : ℤ)
    (x : LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :
    stringBaseComponent a c η hc θ hχ d W ℓ (stringBaseComponent a c η hc θ hχ d W m x)=
      if ℓ=m then stringBaseComponent a c η hc θ hχ d W m x else 0 := by
  split_ifs with h
  · apply Subtype.ext; apply Subtype.ext
    exact (associatedComponent_twice a c η hc θ d W ℓ m x.val.val).trans (ite_eq_left h)
  · apply Subtype.ext; apply Subtype.ext
    exact (associatedComponent_twice a c η hc θ d W ℓ m x.val.val).trans (ite_eq_right h)

end ElementaryPositivity.RawShuffle
end
end OAI

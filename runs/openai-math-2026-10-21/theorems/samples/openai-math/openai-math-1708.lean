namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

@[simp] theorem allocatedMixedFullArray_noise {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (x) :
    allocatedReadNoise (allocatedMixedFullArray smooth deck continuous) x = smooth (.inl x) := rfl

end Erdos3.VectorPolynomial
end
end OAI

set_option warningAsError true

@[expose] public section

noncomputable section

universe uR uM uσ

open TensorProduct

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)

variable (M : Type uM) [AddCommGroup M] [Module R M]

theorem ofTensorProduct_bijective_of_finite_of_projective
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (ofTensorProduct I M) :=
  ⟨ofTensorProduct_injective_of_projective I M,
    ofTensorProduct_surjective_of_finite I M⟩

end AdicCompletion
end
end

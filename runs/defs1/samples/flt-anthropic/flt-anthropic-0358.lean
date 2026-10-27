set_option autoImplicit false

noncomputable section

namespace M4aHerbrand.GenuineDescent

open NumberField TensorProduct IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def genuineDescentOfTensorEquiv
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) :
    IdeleGaloisDescent (𝓞 L) K L :=
  genuineDescent (bgenOfTensorEquiv K L te hte) (continuous_genuineβ K L)

end Genuine
end M4aHerbrand.GenuineDescent
end

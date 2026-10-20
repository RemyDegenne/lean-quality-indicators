public section

open scoped TensorProduct

universe u v w x

namespace TauCeti.HopfIdeal

section Hopf

variable {R : Type u} {H : Type v} {K : Type w}

variable [CommRing R] [Ring H] [Ring K]

variable [HopfAlgebra R H] [HopfAlgebra R K]

@[simp]
theorem kerOfSurjective_toIdeal (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerOfSurjective f hf).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  f.kerOfComul_toIdeal _

end Hopf
end TauCeti.HopfIdeal
end

public section

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v w

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[simp]
theorem charOfPoint_inclusion_ofAdd_one (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    DiagonalizableGroup.charOfPoint (inclusion n f).ofConv (Multiplicative.ofAdd (1 : ℤ)) =
      (RootsOfUnityGroup.pointsMulEquiv n f : Aˣ) := by
  rw [charOfPoint_inclusion, MonoidHom.comp_apply, toMultiplicativeZMod_ofAdd_one]
  apply Units.ext
  rw [DiagonalizableGroup.charOfPoint_apply_coe, pointsMulEquiv_apply]

end RootsOfUnityGroup
end TauCeti
end

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v

variable {K : Type u} [Field K]

section Decomposition

variable [Invertible (2 : K)]

theorem RegularFormClass.anisotropicPart_nsmul_hyperbolicClass_add (m : ℕ)
    (c : RegularFormClass K) :
    RegularFormClass.anisotropicPart (m • hyperbolicClass K + c) =
      RegularFormClass.anisotropicPart c :=
  RegularFormClass.anisotropicPart_eq (RegularFormClass.anisotropic_anisotropicPart c)
    (nsmul_hyperbolicClass_add_wittDecomposition m c)

end Decomposition
end TauCeti
end

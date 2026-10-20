set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech

attribute [instance] GradedModule.acg GradedModule.modR

section GradAltC

variable {R : Type u} [CommRing R] {n : ℕ}

variable (D : GradedModule R n)

def GradedModule.H : ℕ → Type u
  | 0 => LinearMap.ker (GradedModule.d D 0)
  | (i + 1) =>
      LinearMap.ker (GradedModule.d D (i + 1)) ⧸
        (LinearMap.range (GradedModule.d D i)).comap
          (LinearMap.ker (GradedModule.d D (i + 1))).subtype

end GradAltC
end ProjSpaceCech
end

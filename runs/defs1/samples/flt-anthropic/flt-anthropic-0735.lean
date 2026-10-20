set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech

attribute [instance] GradedModule.acg GradedModule.modR

section IsFG

variable {R : Type u} [CommRing R] {n : ℕ}

attribute [instance] GradedModule.Presentation.fJ

abbrev GradedModule.Presentation.ker {D : GradedModule R n} (σ : GradedModule.Presentation D) :
    GradedModule R n :=
  GradedModule.sub σ.F σ.K (GradedModule.Presentation.K_xMul_stable σ)

end IsFG
end ProjSpaceCech
end

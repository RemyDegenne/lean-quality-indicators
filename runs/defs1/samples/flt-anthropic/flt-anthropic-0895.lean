set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech

attribute [instance] GradedModule.acg GradedModule.modR

section IsFG

variable {R : Type u} [CommRing R] {n : ℕ}

attribute [instance] GradedModule.Presentation.fJ

def GradedModule.Presentation.kerIncl {D : GradedModule R n} (σ : GradedModule.Presentation D) :
    GradedModule.Hom σ.ker σ.F where
  toLinearMap := LinearMap.id
  mem_grade _ _ hm := hm.1
  xMul_comm _ := rfl

end IsFG
end ProjSpaceCech
end

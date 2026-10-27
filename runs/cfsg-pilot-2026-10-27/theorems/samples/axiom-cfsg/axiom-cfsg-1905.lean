public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

open MonAux

theorem diagE_injective : Function.Injective diagE := by
  intro c c' h
  funext i
  have h1 := congrArg (fun g : G12 => pr (g (pairVec i (1, 0))) i) h
  simp only [pr_diagE, pr_pairVec_self] at h1
  exact omegaPow_injective_one _ _ h1

end CFSG.GF2Type.Smith1979.IdxFour
end

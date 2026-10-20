@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section4

theorem ThetaCommutator.classicalWordCommutatorExpansion_left_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum := by
  exact Classical.Commutator.classicalWordCommutatorExpansion_left_derivative
    w f g hf i x

end AVenhance.Infra.Section4
end
end

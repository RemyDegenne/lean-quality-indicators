@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sd_spaceGrad_add {f g : Vec 2 → ℝ} {x : Vec 2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    spaceGrad (fun y => f y + g y) x i = spaceGrad f x i + spaceGrad g x i := by
  simp only [spaceGrad]
  rw [fderiv_fun_add hf hg]
  rfl

end AVenhance.Infra.Section5.Contracts
end
end

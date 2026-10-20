@[expose] public section

open MeasureTheory Homogenization

open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sds_gradMatrix_entry_periodic {F : Vec 2 → Vec 2} (hF : Differentiable ℝ F)
    (he : ∀ k x, F (x + latticeShift k) = F x + latticeShift k) (i j : Fin 2) :
    IsZ2Periodic (fun x => gradMatrix F x i j) := by
  have hp := Infra.Section4.amnr_fderiv_periodic_of_equivariant hF he
  intro k x
  change fderiv ℝ (fun y => F y j) (x + latticeShift k) (basisVec i) =
    fderiv ℝ (fun y => F y j) x (basisVec i)
  rw [fderiv_apply (hF _) j, fderiv_apply (hF _) j, hp k x]

end AVenhance.Infra.Section5.Contracts
end
end

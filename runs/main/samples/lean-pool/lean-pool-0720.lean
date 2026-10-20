public section

open Set

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

theorem sum_spatialSecondPartial_eq_sum_multiPartial (g : ParabolicPoint → ℝ) (x : Vec3) (t : ℝ) :
    ∑ j : Fin 3, spatialSecondPartial g j j (x, t) =
      ∑ j : Fin 3, multiPartial g (Pi.single j 2) (x, t) := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact spatialSecondPartial_eq_multiPartial_single g j x t

end CIV
end
end

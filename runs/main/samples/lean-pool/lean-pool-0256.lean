public section

open Set

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

theorem vorticity_second_derivative_equation {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hcl : IsClassicalSolutionOn u p f unitCylinder) :
    ∀ z ∈ unitCylinder, ∀ i j l : Fin 3,
      timePartial (fun w => spatialPartial (fun w' => spatialPartial (curlComp u i) j w') l w) z -
          ∑ m, spatialSecondPartial
            (fun w => spatialPartial (fun w' => spatialPartial (curlComp u i) j w') l w) m m z =
        ∑ m, spatialPartial (fun w => spatialPartial
            (fun w' => spatialPartial (serrinVortFlux u f i m) j w') l w) m z := by
  intro z hz i j l
  exact heat_divergence_equation_spatialPartial
    (contDiffOn_spatialPartial (contDiffOn_curlComp_unitCylinder hcl.1 i) j)
    (fun m => contDiffOn_spatialPartial (contDiffOn_serrinVortFlux hcl i m) j)
    (fun z hz => vorticity_first_derivative_equation hcl z hz i j) l z hz

end CIV
end
end

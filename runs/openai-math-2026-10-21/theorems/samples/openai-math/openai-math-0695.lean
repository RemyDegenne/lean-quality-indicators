namespace OAI

noncomputable section

namespace ScalarConductivity

open Set Filter Topology MeasureTheory Matrix

lemma coordinate_flux_pairing (F : Coord3 → Coord3) (ψ : SmoothScalar Coord3) (x : Coord3) :
    fderiv ℝ ψ.val x (F x)=∑ i,F x i*(smoothDirection (Pi.single i 1) ψ).val x :=
  pi_clm_apply_sum _ _

end ScalarConductivity
end
end OAI

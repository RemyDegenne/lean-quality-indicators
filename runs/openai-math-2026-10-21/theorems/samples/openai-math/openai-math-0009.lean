namespace OAI

noncomputable section

namespace ScalarConductivity

open Set Filter Topology MeasureTheory Matrix

open scoped Matrix.Norms.Elementwise

lemma flux_translate_weak {F : Coord3 → Coord3} {U : Set Coord3} (c : Coord3)
    (hF : ∀ ψ : SmoothScalar Coord3,HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val⊆(fun x => x-c) ⁻¹' U) :
    (∫ x,fderiv ℝ ψ.val x (F (x-c)))=0 := by
  let φ : SmoothScalar Coord3 := ⟨fun y => ψ.val (y+c),
    (smoothScalar_contDiff ψ).comp (contDiff_id.add contDiff_const)⟩
  have hφc : HasCompactSupport φ.val := hc.comp_homeomorph (Homeomorph.addRight c)
  have hφs : tsupport φ.val⊆U := by
    intro y hy
    have hh : y+c∈tsupport ψ.val := tsupport_comp_subset_preimage ψ.val
      (continuous_id.add continuous_const) hy
    simpa only [mem_preimage,add_sub_cancel_right] using hs hh
  calc
    _ = ∫ y,fderiv ℝ ψ.val (y+c) (F y) := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x => fderiv ℝ ψ.val x (F (x-c))) c).symm
    _ = ∫ y,fderiv ℝ φ.val y (F y) := by simp only [φ,fderiv_comp_add_right]
    _ = 0 := hF φ hφc hφs

end ScalarConductivity
end
end OAI

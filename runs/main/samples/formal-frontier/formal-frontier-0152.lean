@[expose] public section

set_option warningAsError true

open Polynomial

noncomputable section

namespace IsKrasner

variable {K L : Type*} [Field K] [NormedField L] [Algebra K L] [IsKrasner K L]

section Quantitative

variable {K₀ L₀ : Type*} [NormedField K₀] [NormedField L₀]
  [NormedAlgebra K₀ L₀] [IsKrasner K₀ L₀]

theorem adjoin_rootSet_le_adjoin_rootSet_of_norm_coeff_sub_lt
    {f g : K₀[X]} {ε : ℝ}
    (hε : 0 < ε)
    (hfm : f.Monic)
    (hgm : g.Monic)
    (hfsep : f.Separable)
    (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε)
    (hfsplit : (f.map (algebraMap K₀ L₀)).Splits)
    (hgsplit : (g.map (algebraMap K₀ L₀)).Splits)
    (hbound : ∀ x ∈ f.rootSet L₀, ∀ x' : L₀,
      IsConjRoot K₀ x x' → x ≠ x' →
        ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖x‖ 1 <
          ‖x - x'‖) :
    IntermediateField.adjoin K₀ (f.rootSet L₀) ≤
      IntermediateField.adjoin K₀ (g.rootSet L₀) := by
  apply adjoin_rootSet_le_adjoin_rootSet_of_forall_exists_close hfsep hfsplit
  intro x hx
  obtain ⟨y, hy, hxy⟩ :=
    exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε (mem_rootSet.mp hx).2
      hfm hgm hdeg hcoeff hgsplit
  refine ⟨y, ?_, fun x' hx' hne ↦ hxy.trans (hbound x hx x' hx' hne)⟩
  rw [mem_rootSet']
  exact mem_aroots'.mp hy

end Quantitative
end IsKrasner
end
end

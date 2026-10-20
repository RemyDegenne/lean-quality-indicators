public section

open MeasureTheory Set

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

theorem volume_axis_eq_zero : volume {x : Vec3 | x 0 = 0 ∧ x 1 = 0} = 0 := by
  set s : Submodule ℝ Vec3 :=
    { carrier := {x : Vec3 | x 0 = 0 ∧ x 1 = 0}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
      smul_mem' := fun c {a} ha => ⟨by simp [ha.1], by simp [ha.2]⟩ }
  with hs_def
  have hne : s ≠ ⊤ := by
    intro htop
    have hmem : (basisVec 0 : Vec3) ∈ s := htop ▸ Submodule.mem_top
    have h0 : (basisVec 0 : Vec3) 0 = 0 := hmem.1
    simp at h0
  have hvol := MeasureTheory.Measure.addHaar_submodule (volume : Measure Vec3) s hne
  simpa [hs_def] using hvol

end CIV
end
end

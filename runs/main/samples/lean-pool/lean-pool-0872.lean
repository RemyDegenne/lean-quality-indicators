@[expose] public section

open ValuativeRel IsDiscreteValuationRing MeasureTheory

open scoped ENNReal

namespace MassFormula

section Integers

variable {K : Type*} [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K] {π : 𝒪[K]} {x : SeparableClosure K}

omit [IsUniformAddGroup K] in
theorem image_coord_eq_imageLattice (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (z : ↥(integers (IntermediateField.adjoin K {x}))) :
    coord hπ hint hei '' {y | addVal ↥(integers (IntermediateField.adjoin K {x})) z ≤
        addVal ↥(integers (IntermediateField.adjoin K {x})) y} =
      imageLattice (Algebra.leftMulMatrix (basisOfEisenstein hπ hint hei) z) := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (toCoeff_equivFun_mem_imageLattice_iff hπ hint hei z y).mpr hy
  · intro ha
    -- the lattice sits in the integer box, so `a` is the chart image of some element
    rw [imageLattice_eq_image_range] at ha
    obtain ⟨c, hcmem, hc⟩ := ha
    refine ⟨(basisOfEisenstein hπ hint hei).equivFun.symm c, ?_, ?_⟩
    · refine (toCoeff_equivFun_mem_imageLattice_iff hπ hint hei z _).mp ?_
      rw [LinearEquiv.apply_symm_apply]
      exact (toCoeff_mem_imageLattice_iff _ c).mpr hcmem
    · rw [coord, LinearEquiv.apply_symm_apply, hc]

end Integers
end MassFormula
end

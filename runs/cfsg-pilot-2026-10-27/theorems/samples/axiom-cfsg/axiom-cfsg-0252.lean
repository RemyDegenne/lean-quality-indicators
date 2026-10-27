public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barX_Zc_le_barCenterX {X S : Subgroup G} (hS : S ≤ X) :
    barX 3 X (Zc S) ≤ barCenterX 3 X S := by
  intro ζ hζ
  rw [mem_barCenterX_iff]
  obtain ⟨z, hz, rfl⟩ := mem_barX_iff.1 hζ
  have hzZ := mem_Zc.1 hz
  refine ⟨mem_barX_iff.2 ⟨z, hzZ.1, rfl⟩, fun u hu => ?_⟩
  obtain ⟨r, hr, rfl⟩ := mem_barX_iff.1 hu
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hzZ.2 r hr)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
end

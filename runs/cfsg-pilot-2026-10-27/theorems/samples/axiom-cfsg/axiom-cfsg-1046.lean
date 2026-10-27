public section

namespace CFSG.Quasithin

open CFSG.OddStandard.Seitz77.L34 CFSG.ComponentClassification.PSL3Four
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

namespace S143

namespace InspW2

theorem center_psl34_eq_bot : Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hcent : (x : Equiv.Perm (Fin 42)) ∈
      Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    rw [Subgroup.mem_inf]
    refine ⟨?_, S_le_R x.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, hg⟩)
  rw [centralizer_S_inf_R, Subgroup.mem_bot] at hcent
  exact Subtype.ext hcent

end InspW2
end S143
end CFSG.Quasithin
end

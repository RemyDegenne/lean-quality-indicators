namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter

open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

variable {G : Type uG} [Group G]

theorem gaugedRepresentation_star (e : G ≃* G) (χ : G →* unitary ℂ) (g : G) :
    star (gaugedRepresentation e χ g) = gaugedRepresentation e χ g⁻¹ := by
  simp only [gaugedRepresentation_apply, star_smul, map_inv]
  have hg : star (groupUnitary (e g)) = groupUnitary ((e g)⁻¹) :=
    Subtype.ext (leftRegular_star _)
  rw [hg]
  congr 1

end FreeGroupFactorMain
end
end OAI

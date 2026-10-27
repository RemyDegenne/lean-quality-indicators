public section

namespace CFSG.RankThree.PartOne.LIT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  (H : Subgroup (V ≃ₗ[ZMod p] V))

variable {H}

namespace PlaneForms

variable {ωU ωL : LinearMap.BilinForm (ZMod p) V} {U L : Submodule (ZMod p) V}

theorem axisU_ne_zero (hP : PlaneForms ωU ωL U L) {c : V} (hc : c ∈ U) (hc0 : c ≠ 0) :
    ωU c ≠ 0 := by
  obtain ⟨z, -, hz⟩ := hP.nondegU c hc hc0
  intro h0
  exact hz (by rw [h0, LinearMap.zero_apply])

end PlaneForms
end CFSG.RankThree.PartOne.LIT
end

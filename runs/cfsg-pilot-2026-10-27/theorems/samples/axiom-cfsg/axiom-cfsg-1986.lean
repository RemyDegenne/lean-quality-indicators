public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuType
  CFSG.Quasithin.H13.F431.F45

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

section Cosets

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

theorem smul_lv_iff' (c : α.Completion Y) (k : c.G0) :
    k • c.lv = c.lv ↔ (k : Y) ∈ c.φ2.range := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right]

end Cosets
end CFSG.Quasithin.H13.F45Ru
end

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open scoped Pointwise

namespace ReeTag

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

variable {t K a}

theorem reeFixed_mul_unique'
    {h₁ h₂ u₁ u₂ : ModGL t.tag K} (hh₁ : h₁ ∈ t.reeFixedTorus K a)
    (hh₂ : h₂ ∈ t.reeFixedTorus K a) (hu₁ : u₁ ∈ t.reeFixedPosUnipotent K a)
    (hu₂ : u₂ ∈ t.reeFixedPosUnipotent K a) (h : u₁ * h₁ = u₂ * h₂) : u₁ = u₂ ∧ h₁ = h₂ :=
  (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.2.1 h₁ (Subgroup.mem_inf.1 hh₁).1 h₂
    (Subgroup.mem_inf.1 hh₂).1 u₁ (Subgroup.mem_inf.1 hu₁).1 u₂ (Subgroup.mem_inf.1 hu₂).1 h

end ReeTag
end CFSG.LieType.Ree
end

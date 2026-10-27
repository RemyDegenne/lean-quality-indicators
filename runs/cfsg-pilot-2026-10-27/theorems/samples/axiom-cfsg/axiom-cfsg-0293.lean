public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem GGNbrTableBWeylInputOn.of_cover {S T U : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGNbrTableBWeylInputOn S) (h₂ : GGNbrTableBWeylInputOn T)
    (h : ∀ p lab, U p lab → S p lab ∨ T p lab) : GGNbrTableBWeylInputOn U := by
  intro p hp hp2 lab hlab hU hhs hsp
  rcases h p lab hU with hS | hT
  · exact h₁ p hp hp2 lab hlab hS hhs hsp
  · exact h₂ p hp hp2 lab hlab hT hhs hsp

end CFSG.StandardType
end

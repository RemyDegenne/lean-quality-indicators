public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Three

theorem le_normalizer_of_commutator_mem {P E C : Subgroup G}
    (hPE : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ E) (hEC : E ≤ C) (hCP : C ≤ P) :
    P ≤ normalizer (C : Set G) := fun p hp =>
  Sec2.mem_normalizer_of_forall_conj_mem fun c hc => by
    have h := hPE _ hp _ (hCP hc)
    have : p * c * p⁻¹ = (p * c * p⁻¹ * c⁻¹) * c := by group
    rw [this]
    exact mul_mem (hEC h) hc

end Three
end CFSG.ComponentClassification.AS81
end

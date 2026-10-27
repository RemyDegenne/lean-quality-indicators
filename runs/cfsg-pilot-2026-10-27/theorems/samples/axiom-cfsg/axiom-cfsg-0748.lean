public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b

open CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

open CFSG.ComponentClassification.Asc75Lemma31

open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)

include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)

include hP hPC

omit [Finite G] h hP hPC in
theorem conj_commutatorElement (x u v : G) : x * ⁅u, v⁆ * x⁻¹ = ⁅x * u * x⁻¹, x * v * x⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

end PStructure
end Setting310
end CFSG.ComponentClassification.RankTwoAltFive
end

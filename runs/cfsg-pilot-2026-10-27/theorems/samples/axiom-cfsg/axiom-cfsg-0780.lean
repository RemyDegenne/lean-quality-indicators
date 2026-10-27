public section

namespace CFSG.Quasithin.H13.KGH91

open Matrix CFSG.Quasithin.SLnTwo CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm

open scoped Pointwise

variable {G : Type} [Group G] {n : ℕ}

namespace Setting

variable [Finite G] {T L V V₁ V₂ : Subgroup G} (S : Setting G T L V V₁ V₂ n)

include S

theorem pairing_conj {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (h₁ : m ∈ Subgroup.normalizer (V₁ : Set G)) (h₂ : m ∈ Subgroup.normalizer (V₂ : Set G)) :
    ∀ a ∈ V₁, ∀ c ∈ V₂, pairing S.C₁ S.C₂ (m * a * m⁻¹) (m * c * m⁻¹) =
      pairing S.C₁ S.C₂ a c := by
  have hβ := isDualPairing S.C₁ S.C₂ S.dual
  have m₁ : ∀ a ∈ V₁, m * a * m⁻¹ ∈ V₁ := fun a ha => (Subgroup.mem_normalizer_iff.1 h₁ a).1 ha
  have m₂ : ∀ c ∈ V₂, m * c * m⁻¹ ∈ V₂ := fun c hc => (Subgroup.mem_normalizer_iff.1 h₂ c).1 hc
  refine eq_pairing S.hn S.C₁ S.C₂ S.dual (fun a ha b hb c hc => ?_) (fun a ha c hc d hd => ?_)
    (fun l hl a ha c hc => ?_) ?_
  · have e : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
    rw [e, hβ.1 _ (m₁ a ha) _ (m₁ b hb) _ (m₂ c hc)]
  · have e : m * (c * d) * m⁻¹ = (m * c * m⁻¹) * (m * d * m⁻¹) := by group
    rw [e, hβ.2.1 _ (m₁ a ha) _ (m₂ c hc) _ (m₂ d hd)]
  · have hl' : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hm l).1 hl
    have e : ∀ x, m * (l * x * l⁻¹) * m⁻¹ = (m * l * m⁻¹) * (m * x * m⁻¹) * (m * l * m⁻¹)⁻¹ :=
      fun x => by group
    rw [e, e]
    exact hβ.2.2.2.2 _ hl' _ (m₁ a ha) _ (m₂ c hc)
  · obtain ⟨a', ha', ha'1⟩ := S.exists_ne_one₁
    obtain ⟨c', hc', hac'⟩ := hβ.2.2.1 a' ha' ha'1
    refine ⟨m⁻¹ * a' * m, ?_, m⁻¹ * c' * m, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h₁) a').1 ha'
      rwa [inv_inv] at this
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h₂) c').1 hc'
      rwa [inv_inv] at this
    · have e : ∀ x, m * (m⁻¹ * x * m) * m⁻¹ = x := fun x => by group
      rw [e, e, hac']
      exact one_ne_zero

end Setting
end CFSG.Quasithin.H13.KGH91
end

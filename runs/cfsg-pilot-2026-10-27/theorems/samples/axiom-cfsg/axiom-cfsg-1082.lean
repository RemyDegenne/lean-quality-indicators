public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_l34K_le {L H : Subgroup G} {u : G}
    (h : ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      ⁅H, K₁⁆ ≤ oddIn (centralizer ({u} : Set G))) :
    ⁅H, l34K L u⁆ ≤ oddIn (centralizer ({u} : Set G)) := by
  set C := centralizer ({u} : Set G) with hC
  have hconjO : ∀ c ∈ C, ∀ x ∈ oddIn C, c * x * c⁻¹ ∈ oddIn C := fun c hc x hx =>
    (mem_normalizer_iff.mp (normalizer_le_normalizer_oddIn C (le_normalizer hc)) x).mp hx
  let M : Subgroup G :=
    { carrier := {g | g ∈ C ∧ ∀ x ∈ H, x * g * x⁻¹ * g⁻¹ ∈ oddIn C}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun x hx => by
        have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem (ha.2 x hx) (hconjO a ha.1 _ (hb.2 x hx))⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun x hx => by
        have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hconjO a⁻¹ (inv_mem ha.1) _ (inv_mem (ha.2 x hx))⟩ }
  have hKM : l34K L u ≤ M := by
    refine iSup_le fun K₁ => iSup_le fun hK₁ => iSup_le fun hK₁p => iSup_le fun hK₁Y => ?_
    intro g hg
    refine ⟨hK₁ hg, fun x hx => ?_⟩
    have := h K₁ hK₁ hK₁p hK₁Y (commutator_mem_commutator hx hg)
    rwa [commutatorElement_def] at this
  rw [commutator_le]
  intro x hx g hg
  rw [commutatorElement_def]
  exact (hKM hg).2 x hx

end CFSG.ComponentClassification.GrSLit.GrS5
end

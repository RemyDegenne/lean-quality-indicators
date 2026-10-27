public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem commutator_cW_le
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    ⁅cW W, W⁆ ≤ preimageOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  have hcard := hJ.card_piSub_V0 hKC hW hUW
  obtain ⟨ζ, hζS, hζ1, hζc, hζR, -⟩ := sylow_centralizer_facts (piSub_le_P _ _) hcard
  have hζP : ζ ∈ P := piSub_le_P _ _ hζS
  have hWM : W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := hW.le
  rw [commutator_le]
  intro c hc w' hw'
  have hcM := hWM (mem_inf.mp hc).1
  have hwM := hWM hw'
  have hcwM : ⁅c, w'⁆ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hcM hwM) (inv_mem hcM)) (inv_mem hwM)
  rw [mem_preimageOf hcwM, ← hJ.theta_eq_one_iff]
  have heq' : (⟨⁅c, w'⁆, hcwM⟩ :
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) =
      ⁅(⟨c, hcM⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))),
        ⟨w', hwM⟩⁆ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have heq : (QuotientGroup.mk ⟨⁅c, w'⁆, hcwM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      ⁅(QuotientGroup.mk ⟨c, hcM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        QuotientGroup.mk ⟨w', hwM⟩⁆ := by
    rw [heq']
    exact map_commutatorElement (QuotientGroup.mk' _) _ _
  rw [heq]
  refine hJ.theta_commutator_eq_one hζP hζ1 hζc hζR ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    have h1 : (v : X) * c = c * v := mem_centralizer_iff.mp (mem_inf.mp hc).2 _ hv
    change (QuotientGroup.mk (⟨c, hcM⟩ * v) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk (v * ⟨c, hcM⟩)
    rw [show (⟨c, hcM⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) * v =
      v * ⟨c, hcM⟩ from Subtype.ext h1.symm]
  · rintro _ ⟨v, hv, rfl⟩
    have h1 : w'⁻¹ * v * w' ∈ W ⊓ oP W := by
      have := conj_mem_inf' conj_mem_W conj_mem_oP w'⁻¹ (inv_mem (le_normalizer_self hw'))
        (v : X) hv
      rwa [inv_inv] at this
    refine ⟨⟨w', hwM⟩⁻¹ * v * ⟨w', hwM⟩, h1, ?_⟩
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end EndB.JLayer
end CFSG.ComponentClassification.HarrisLit
end

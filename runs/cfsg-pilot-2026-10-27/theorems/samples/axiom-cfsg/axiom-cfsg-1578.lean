public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

open SymplecticHigher (flagStabilizer fieldSp)

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

variable (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)

theorem sp_model_comm [Finite K] [CharP K 2] (hr : 2 ≤ r) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r)
    {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hbig : 1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b) {α₁ α₂ : MulAut (StatedSp r K)}
    (h₁ : Odd (orderOf α₁)) (h₂ : Odd (orderOf α₂)) (h₁₂ : Odd (orderOf ⁅α₁, α₂⁆))
    (hn₁ : SpNormFix (fun i hi => (hI i hi).2) htI α₁)
    (hn₂ : SpNormFix (fun i hi => (hI i hi).2) htI α₂) : ⁅α₁, α₂⁆ = 1 := by
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hI₁ : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  obtain ⟨g₁, σ₁, hg₁⟩ := exists_data hr hI htI h₁ hn₁
  obtain ⟨g₂, σ₂, hg₂⟩ := exists_data hr hI htI h₂ hn₂
  have hσ₁ : σ₁ = 1 := sigma_eq_one hI₀ htI hI₁ hmax hbig hn₁ hg₁
  have hσ₂ : σ₂ = 1 := sigma_eq_one hI₀ htI hI₁ hmax hbig hn₂ hg₂
  subst hσ₁ hσ₂
  have hC : spFlagLeviHom hI₀ htI ⁅g₁, g₂⁆ = 1 := by
    refine leviHom_eq_one_of_blocks hI₀ htI (fun b hb => ?_) ?_
    · rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact cutHom_commute hI₀ htI hI₁ hn₁ hn₂ hg₁ hg₂ hb
    · rw [map_commutatorElement]
      refine eq_one_of_commute_spResBlock (r - t)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) ?_
      intro c hc
      have hc₁ : Commute (spFlagResHom hI₀ htI g₁) c :=
        resHom_commute_spResBlock hI₀ htI hmax hn₁ hg₁ hc
      have hc₂ : Commute (spFlagResHom hI₀ htI g₂) c :=
        resHom_commute_spResBlock hI₀ htI hmax hn₂ hg₂ hc
      rw [commutatorElement_def]
      exact ((hc₁.mul_left hc₂).mul_left hc₁.inv_left).mul_left hc₂.inv_left
  obtain ⟨n, hn⟩ := isPGroup_ker_spFlagLeviHom hI₀ htI hI₁
    (⟨⁅g₁, g₂⁆, MonoidHom.mem_ker.mpr hC⟩ : (spFlagLeviHom hI₀ htI).ker)
  have hpow : (⁅g₁, g₂⁆ : flagStabilizer r K I) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hpow' : (⁅(g₁ : StatedSp r K), (g₂ : StatedSp r K)⁆ : StatedSp r K) ^ 2 ^ n = 1 := by
    have := congrArg (flagStabilizer r K I).subtype hpow
    rwa [map_pow, map_commutatorElement, map_one] at this
  have hα₁ : α₁ = MulAut.conj (g₁ : StatedSp r K) := by
    ext x
    rw [hg₁, map_one, MulAut.one_apply, MulAut.conj_apply]
  have hα₂ : α₂ = MulAut.conj (g₂ : StatedSp r K) := by
    ext x
    rw [hg₂, map_one, MulAut.one_apply, MulAut.conj_apply]
  rw [hα₁, hα₂, ← map_commutatorElement] at h₁₂ ⊢
  have hdvd : orderOf (MulAut.conj ⁅(g₁ : StatedSp r K), (g₂ : StatedSp r K)⁆) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow', map_one])
  have h1 : orderOf (MulAut.conj ⁅(g₁ : StatedSp r K), (g₂ : StatedSp r K)⁆) = 1 :=
    (Nat.Coprime.pow_right n h₁₂.coprime_two_right).eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.mp h1

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
end

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace WCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem not_fstar_le_wQ [CaseIAmbient T] (cfg : WCfg K z J zJ H S) :
    ¬ genFittingFStar T ≤ wQ K := by
  intro hFQ
  haveI hFn : (genFittingFStar T).Normal := genFittingFStar_normal T
  have hFHt : genFittingFStar T ≤ firstFactor K := hFQ.trans (wQ_le K)
  obtain ⟨e⟩ := cfg.ht
  let ψ : ↥(genFittingFStar T) →* G192 := e.toMonoidHom.comp
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion hFHt))
  have hψW : ∀ f : ↥(genFittingFStar T), ψ f ∈ W192.w192W :=
    fun f => cfg.mk_mem_W_of_mem_Q e (hFQ f.2)
  rcases ψ.normal_ker.eq_bot_or_eq_top with hk | hk
  ·
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hk
    obtain ⟨a, b, hab⟩ :=
      (CaseIAmbient.fstar_nonabelian : ∃ a b : ↥(genFittingFStar T), a * b ≠ b * a)
    exact hab (hinj (by rw [map_mul, map_mul]; exact W192.w192W_mul_comm (hψW a) (hψW b)))
  ·
    have hle : (genFittingFStar T).subgroupOf (firstFactor K) ≤
        classicalInvolutionOddCore ↥(firstFactor K) := by
      intro x hx
      have h1 : ψ ⟨(x : T), hx⟩ = 1 := by
        have : (⟨(x : T), hx⟩ : ↥(genFittingFStar T)) ∈ ψ.ker := hk ▸ Subgroup.mem_top _
        exact this
      have h2 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)))
          (Subgroup.inclusion hFHt ⟨(x : T), hx⟩) = 1 :=
        e.injective (h1.trans e.map_one.symm)
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h2
    have hodd : Odd (Nat.card ↥(genFittingFStar T)) := by
      have h := Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥(firstFactor K))
        (Subgroup.card_dvd_of_le hle)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFHt).toEquiv] at h
    have hFO : genFittingFStar T ≤ classicalInvolutionOddCore T :=
      CFSG.ComponentClassification.OddCore.maximal T _ hFn hodd
    rw [CaseIAmbient.oddCore_eq_bot (T := T), le_bot_iff] at hFO
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hFO

end WCfg
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
end

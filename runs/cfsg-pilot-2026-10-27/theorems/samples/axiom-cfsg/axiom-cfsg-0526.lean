public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

open CFSG.LargeExtraspecial (pointRadical mem_pointRadical card_pointRadical)

open CFSG.LargeExtraspecial.S2 (perp mem_perp)

open scoped commutatorElement Pointwise

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)

include H

theorem commutator_SHat_le (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs)
    (hz₂z : z₂ ∉ zpowers z) :
    ⁅sec3SHat (Q₀ ⊔ Q) Zs, sec3SHat (Q₀ ⊔ Q) Zs⁆ ≤ Zs := by
  set S := sec3SHat (Q₀ ⊔ Q) Zs with hS
  set U' := (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) with hU'
  have hSC : S ≤ sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSU : ⁅S, U'⁆ ≤ Zs := (Subgroup.commutator_le).mpr fun s hs u hu => by
    rw [commutatorElement_def]
    exact H.commutator_mem_Zs_of_mem_U hΩ hQF hZQ hz₂ hz₂z hs hu
  have hZS : ⁅Zs, S⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro w hw
    exact mem_centralizer_iff.mpr fun s hs => (mem_centralizer_iff.mp (hSC hs).2 w hw).symm
  have h1 : ⁅⁅S, U'⁆, S⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hSU le_rfl).trans hZS.le)
  have h2 : ⁅⁅U', S⁆, S⁆ = ⊥ := by rw [commutator_comm U' S]; exact h1
  have h3 : ⁅⁅S, S⁆, U'⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have hSSU : ⁅S, S⁆ ≤ U' := (Subgroup.commutator_le).mpr fun s hs t ht => by
    have hsF := (hSC hs).1
    have htF := (hSC ht).1
    have hcF : ⁅s, t⁆ ∈ sec3F (Q₀ ⊔ Q) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hsF htF) (inv_mem hsF)) (inv_mem htF)
    have hcS : ⁅s, t⁆ ∈ S := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hs ht) (inv_mem hs)) (inv_mem ht)
    refine H.mem_U_of_mem_SHat hQF hZQ (s := ⟨_, hcF⟩) hcS ?_
    have e : (⟨⁅s, t⁆, hcF⟩ : ↥(sec3F (Q₀ ⊔ Q))) =
        ⁅(⟨s, hsF⟩ : ↥(sec3F (Q₀ ⊔ Q))), ⟨t, htF⟩⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Sec3SHat.comm_of_mem_pointRadical H.xsub.q_nondegenerate (H.cl_ne_zero hZQ hz₂ hz₂z)
      (H.q_cl_eq_zero hZQ hz₂) (H.ρF_mem_pointRadical hΩ hQF hZQ hz₂ hz₂z hs)
      (H.ρF_mem_pointRadical hΩ hQF hZQ hz₂ hz₂z ht)
  rw [← H.centerIn_U hZQ hz₂ hz₂z]
  intro c hc
  exact ⟨hSSU hc, (commutator_eq_bot_iff_le_centralizer.mp h3) hc⟩

end Sec38Hyp
end CFSG.ComponentClassification.AS81
end

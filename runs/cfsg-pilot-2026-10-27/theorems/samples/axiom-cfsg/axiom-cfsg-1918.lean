public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

section Chain

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G} {n : ℕ}

namespace IsTranslationSubgroup

variable {L L₀ Y V : Subgroup G} {Γ : Set G}

theorem isBenderGroup_commutator (hH : Th91Hyp D hC)
    (hs : IsSimpleGroup (commutator G)) (h3 : Conclusion9_3 D hC) (h4 : Conclusion9_4 D hC T S)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) :
    IsBenderGroup (commutator G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := commutator G with hKdef
  have : IsSimpleGroup K := hs
  obtain ⟨hn, -⟩ := hU.two_le_and_card_eq_of_psu3 hH ⟨eH⟩
  obtain ⟨eJ⟩ := nonempty_pResidualOf_mulEquiv_psu3 h3 hCH eH
  have hLB : IsBenderGroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := .isPSU3 n hn eJ
  have hLK := le_commutator_of_isBenderGroup hLB
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
    refine ⟨⟨a, hLK a.2⟩, ⟨b, hLK b.2⟩, fun h => hab ?_⟩
    have h' := congrArg (fun x : K => (x : G)) h
    exact Subtype.ext h'
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzK : z ∈ K := mem_commutator_of_mem_omega hU hz
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huD : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
  have huzD : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hz, rfl⟩
  have hzS : z ∈ (S : Subgroup G) := by
    have := (S : Subgroup G).mul_mem huD.1 huzD.1
    rwa [← mul_assoc, hu2, one_mul] at this
  obtain ⟨hSK, -⟩ := inter_commutator_eq hH h3 h4 hU hCH eH hUn hL hΓ hY hV rfl
  obtain ⟨hcard, -, -⟩ := card_sup_and_mem hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hRVz : ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ⊔ V ≤
        Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun r hr => ?_) (fun v hv => ?_)
    · have hrB : r ∈ Subgroup.centralizer ((S : Set G) ∩ D) :=
        hL.centralizer_eq ▸ Subgroup.mem_sup_left hr.1
      have h1 : Commute r hC.d := (Subgroup.mem_centralizer_iff.mp hrB _ huD).symm
      have h2 : Commute r (hC.d * z) := (Subgroup.mem_centralizer_iff.mp hrB _ huzD).symm
      have h12 := h1.mul_right h2
      rw [← mul_assoc, hu2, one_mul] at h12
      exact Subgroup.mem_centralizer_singleton_iff.mpr h12.eq
    · have := hV.isElementaryAbelian
      have h := congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := V)).comm ⟨v, hv⟩ ⟨z, hV.le hz⟩)
      exact Subgroup.mem_centralizer_singleton_iff.mpr h
  obtain ⟨P, hP⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 K S
  have hPeq : ((P : Subgroup K)).map K.subtype = (S : Subgroup G) ⊓ K := by
    rw [hP, Subgroup.subgroupOf_map_subtype]
  have hz'P : (⟨z, hzK⟩ : K) ∈ (P : Subgroup K) := by
    rw [hP]
    exact Subgroup.mem_subgroupOf.mpr hzS
  refine isBenderGroup_of_wcl_abelian hnonab P hz'P (fun h => hz1' (congrArg Subtype.val h))
    (fun x hx => Subtype.ext ?_)
    (isMulCommutative_wcl hH h3 h4 hU hCH eH hUn hL hΓ hY hV hz hz1' hzK) ?_
  · have hxRV : (x : G) ∈ ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ⊔ V := by
      rw [← hSK, ← hKdef, ← hPeq]
      exact ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hRVz hxRV)
  · rw [← Subgroup.card_map_of_injective K.subtype_injective, hPeq, hKdef, hSK, hcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

end IsTranslationSubgroup
end Chain
end CFSG.OddTranspositions.PartThree.Nine
end

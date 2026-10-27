public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
  CFSG.RankThree.PartTwo.Sec14

theorem exists_of_inspectAutLoc {X : Type} [Group X] [Finite X] {P : Subgroup X → Prop}
    (hP : ∀ E : Subgroup (MulAut X), Nat.card E = 9 → (∀ ε ∈ E, ε ^ 3 = 1) → LocE X E →
      IsPGroup 3 (fixE E) →
      ∀ K : Subgroup X, (∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) → Group.IsPerfect K → K ≠ ⊥ →
        IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) →
        Sec4.IsList46 (K ⧸ aschbacherSolvableCore 3 K) →
        K ≤ (⨆ (ε : MulAut X) (_ : ε ∈ E) (_ : ε ≠ 1),
          pPrimeCoreOf 3 (K ⊓ Sec4.autFix ε)) → P K)
    (hθ : ∀ K' : Subgroup X, P K' → aschbacherSolvableCore 3 K' = ⊥)
    {Γ : Type} [Group Γ] [Finite Γ] {A L K : Subgroup Γ} {e : Γ} (h : Sig148 A L K e)
    (hker : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (zpowers e : Set Γ))
    (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) (hloc : LocA A L)
    (hfix : IsPGroup 3 (L3PGL.fixA A L))
    (hK46 : Sec4.IsList46 (K ⧸ aschbacherSolvableCore 3 K)) :
    ∃ K' : Subgroup X, P K' ∧ Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* K') := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.isE27.1.2
  have hAL := h.le_normalizer_L
  have hAK := h.le_normalizer_K
  have hιe : ∀ a : A, actX hAL ψ a = 1 ↔ (a : Γ) ∈ zpowers e := by
    intro a
    rw [actX_eq_one_iff hAL ψ a, ← SetLike.mem_coe, ← hker]
    exact ⟨fun h' => ⟨a.2, h'⟩, fun h' => h'.2⟩
  have he3 : orderOf e = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hA3 e h.mem) h.ne_one
  have hcardE : Nat.card (actX hAL ψ).range = 9 := by
    have hzA : zpowers e ≤ A := zpowers_le.2 h.mem
    have hker' : (actX hAL ψ).ker = (zpowers e).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, mem_subgroupOf, hιe]
    have hk3 : Nat.card (actX hAL ψ).ker = 3 := by
      rw [hker', Nat.card_congr (subgroupOfEquivOfLe hzA).toEquiv, Nat.card_zpowers, he3]
    have h1 := Subgroup.card_mul_index (actX hAL ψ).ker
    rw [Subgroup.index_ker, hk3, h.isE27.2] at h1
    omega
  have hexpE : ∀ ε ∈ (actX hAL ψ).range, ε ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (by simpa using hA3 a a.2), map_one]
  have hinv : ∀ ε ∈ (actX hAL ψ).range, ∀ k ∈ (kappa h.le ψ).range,
      ε k ∈ (kappa h.le ψ).range := by
    rintro _ ⟨a, rfl⟩ _ ⟨k, rfl⟩
    exact ⟨_, (Ronan148K.kappa_actX h.le ψ hAL hAK a k).symm⟩
  haveI : Group.IsPerfect K := h.isPerfect
  have hKbp : Group.IsPerfect (kappa h.le ψ).range := Group.IsPerfect.range _
  have hkerR : (kappa h.le ψ).rangeRestrict.ker = (kappa h.le ψ).ker :=
    MonoidHom.ker_rangeRestrict _
  obtain ⟨χ⟩ := ONLoc.nonempty_thetaQuot_equiv (kappa h.le ψ).rangeRestrict
    (kappa h.le ψ).rangeRestrict_surjective
    (by rw [hkerR]; exact isSolvable_ker_kappa h.le ψ)
    (by
      rw [hkerR]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_ker_kappa h.le ψ))
  have hKbq : IsQuasisimple ((kappa h.le ψ).range ⧸
      aschbacherSolvableCore 3 (kappa h.le ψ).range) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv χ.symm h.isQuasisimple
  have hKb46 : Sec4.IsList46 ((kappa h.le ψ).range ⧸
      aschbacherSolvableCore 3 (kappa h.le ψ).range) :=
    Sec21.Item223PrintProof.isList46_of_mulEquiv χ.symm hK46
  have hgen : (kappa h.le ψ).range ≤ ⨆ (ε : MulAut X) (_ : ε ∈ (actX hAL ψ).range)
      (_ : ε ≠ 1), pPrimeCoreOf 3 ((kappa h.le ψ).range ⊓ Sec4.autFix ε) := by
    have htop : (⊤ : Subgroup K) ≤ ⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
        (pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ))).subgroupOf K := by
      intro k _
      have hk := h.le_iSup k.2
      have hS : ∀ x : Γ, pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ)) ≤ K := fun x => by
        intro y hy
        obtain ⟨c, -, rfl⟩ := hy
        exact (mem_inf.1 c.2).1
      have hmap : (⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
          (pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ))).subgroupOf K).map K.subtype =
          ⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
            pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ)) := by
        simp only [Subgroup.map_iSup, subgroupOf_map_subtype, inf_of_le_left (hS _)]
      rw [← hmap] at hk
      obtain ⟨k', hk', hkk⟩ := hk
      rwa [← Subtype.ext hkk]
    refine (le_of_eq (MonoidHom.range_eq_map (kappa h.le ψ))).trans ((map_mono htop).trans ?_)
    simp only [Subgroup.map_iSup]
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun hxe => ?_
    have hy1 : actX hAL ψ ⟨x, hx⟩ ≠ 1 := fun h1 => hxe ((hιe ⟨x, hx⟩).1 h1)
    exact le_iSup_of_le (actX hAL ψ ⟨x, hx⟩) (le_iSup_of_le ⟨⟨x, hx⟩, rfl⟩
      (le_iSup_of_le hy1 (Ronan148K.map_pPrimeCoreOf_le_autFix h.le ψ hAL hAK hA3 ⟨x, hx⟩)))
  have hPK := hP (actX hAL ψ).range hcardE hexpE (locE_range_actX hAL ψ hloc)
    (by rw [fixE_range_actX hAL ψ]; exact hfix.map _)
    (kappa h.le ψ).range hinv hKbp (Ronan148K.range_kappa_ne_bot h ψ) hKbq hKb46 hgen
  exact ⟨(kappa h.le ψ).range, hPK,
    CFSG.AGLEmbeddingD2.Wilson.Proving.nonempty_quotient_aschbacherSolvableCore_equiv_range
      (kappa h.le ψ) (isSolvable_ker_kappa h.le ψ) (coprime_card_ker_kappa h.le ψ) (hθ _ hPK)⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
end

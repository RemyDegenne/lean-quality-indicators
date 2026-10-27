open CFSG

open scoped Pointwise

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section16_ASet_diff_msigma_exists_prime_compl_zpow
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {a : G}
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G)) :
    ∃ n : ℤ, ∃ q : Nat.Primes,
      orderOf (a ^ n) = q.val ∧
        q ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
  classical
  rcases section16_ASet_diff_msigma_product_decomp (G := G) ha with
    ⟨u, s, huU, hsSigma, hu_ne, ha_eq⟩
  let Sσ : Subgroup M := section10MsigmaSubgroup M
  haveI : Sσ.Normal := by
    simpa [Sσ] using (section10MsigmaSubgroup_normal (M := M))
  let qM : M →* M ⧸ Sσ := QuotientGroup.mk' Sσ
  have haM : a ∈ M := ha.1.1.1
  have huM : u ∈ M := hKU.2.2.2.1.1 huU
  have hsM : s ∈ M := section16_msigma_le (G := G) M hsSigma
  let aM : M := ⟨a, haM⟩
  let uM : M := ⟨u, huM⟩
  let sM : M := ⟨s, hsM⟩
  have hsSσ : sM ∈ Sσ := by
    have hsSub : sM ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf, sM] using hsSigma
    simpa [Sσ, section16_msigma_subgroupOf_eq (M := M)] using hsSub
  have haM_eq : aM = uM * sM := by
    apply Subtype.ext
    simpa [aM, uM, sM] using ha_eq
  have hq_s : qM sM = 1 := by
    exact (QuotientGroup.eq_one_iff (N := Sσ) sM).2 hsSσ
  have hq_a_eq_u : qM aM = qM uM := by
    rw [haM_eq, map_mul, hq_s, mul_one]
  have hu_not_kernel : qM uM ≠ 1 := by
    intro huq
    have huSσ : uM ∈ Sσ :=
      (QuotientGroup.eq_one_iff (N := Sσ) uM).1 huq
    have huSigma : u ∈ section10Msigma M := by
      have huSub : uM ∈ (section10Msigma M).subgroupOf M := by
        simpa [Sσ, section16_msigma_subgroupOf_eq (M := M)] using huSσ
      simpa [Subgroup.mem_subgroupOf, uM] using huSub
    have huJoin : u ∈ K ⊔ section10Msigma M := Subgroup.mem_sup_right huSigma
    have hCompKMsigma :
        section12ComplementIn M (K ⊔ section10Msigma M) U :=
      section16_complement_k_msigma_of_KUData (G := G) hM hKU
    have huBot : u ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hCompKMsigma.2.2.2 huJoin huU
    exact hu_ne (by simpa using huBot)
  let A : Subgroup M := Subgroup.zpowers aM
  let Usub : Subgroup M := U.subgroupOf M
  have huUsub : uM ∈ Usub := by
    simpa [Usub, Subgroup.mem_subgroupOf, uM] using huU
  have hAmap_le_Umap : A.map qM ≤ Usub.map qM := by
    change (Subgroup.zpowers aM).map qM ≤ Usub.map qM
    rw [MonoidHom.map_zpowers, hq_a_eq_u]
    exact Subgroup.zpowers_le.2 (Subgroup.mem_map_of_mem qM huUsub)
  have hqa_mem : qM aM ∈ A.map qM :=
    Subgroup.mem_map_of_mem qM (Subgroup.mem_zpowers aM)
  have hAmap_ne : A.map qM ≠ ⊥ := by
    intro hbot
    have hqa_one : qM aM = 1 := by
      have hqa_bot : qM aM ∈ (⊥ : Subgroup (M ⧸ Sσ)) := by
        simpa [hbot] using hqa_mem
      simpa using hqa_bot
    exact hu_not_kernel (by simpa [hq_a_eq_u] using hqa_one)
  have hcard_ne_one : Nat.card (A.map qM) ≠ 1 := by
    intro hcard
    exact hAmap_ne ((Subgroup.eq_bot_iff_card (H := A.map qM)).2 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨q, hqprime, hqdivAmap⟩
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqdivUmap : q ∣ Nat.card (Usub.map qM) :=
    hqdivAmap.trans (Subgroup.card_dvd_of_le hAmap_le_Umap)
  have hqdivUsub : q ∣ Nat.card Usub :=
    hqdivUmap.trans (Subgroup.card_map_dvd (H := Usub) qM)
  rcases hKU.2.2.2.1 with ⟨_hUM, hUHall⟩
  have hqcompl :
      q' ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
    exact hUHall.p_in_pi_of_p_dvd_card q' (by simpa [q'] using hqdivUsub)
  have hqdivA : q ∣ Nat.card A :=
    hqdivAmap.trans (Subgroup.card_map_dvd (H := A) qM)
  haveI : Fact q.Prime := ⟨hqprime⟩
  rcases exists_prime_orderOf_dvd_card' (G := A) q hqdivA with ⟨zA, hzA_order⟩
  rcases Subgroup.mem_zpowers_iff.mp zA.property with ⟨n, hzA_eq⟩
  refine ⟨n, q', ?_, hqcompl⟩
  have hzG_eq : (((zA : A) : M) : G) = a ^ n := by
    have hzM_eq := congrArg (fun z : M => (z : G)) hzA_eq
    simpa [aM] using hzM_eq.symm
  have hz_order_M : orderOf ((zA : A) : M) = q := by
    simpa [Subgroup.orderOf_coe] using hzA_order
  have hz_order_G : orderOf (((zA : A) : M) : G) = q := by
    simpa [Subgroup.orderOf_coe] using hz_order_M
  simpa [q', ← hzG_eq] using hz_order_G

end MainResults

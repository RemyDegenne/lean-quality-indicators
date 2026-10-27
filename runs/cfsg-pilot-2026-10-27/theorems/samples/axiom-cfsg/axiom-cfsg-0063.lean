public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)

open CFSG.Assembly.RankThreeEven (localRank projSp projSL)

section Final

open Item812Res2 in
theorem sec8B_eq_of_projSp {G : Type} [Group G] [Finite G] (h3 : localRank 3 G ≤ 3)
    {A : Subgroup G} (hAF : A ∈ partTwoF G) (hA81 : Nat.card A = 81) {f : G} (hfA : f ∈ A)
    (hf1 : f ≠ 1) {Lf : Subgroup G} (hLf : Lf ∈ thetaComponentsAt 3 f)
    (hX : Nonempty (Lf ⧸ aschbacherSolvableCore 3 Lf ≃* projSp 2 (GaloisField 2 3)))
    {x : G} (hxA : x ∈ A) (hxout : InducesOuterTheta x Lf) {g : G}
    (hg : g ∈ gammaSet A Lf) :
    sec8B A Lf = Subgroup.closure {f, g} ⊔
      (A ⊓ inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer ({g} : Set G))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₀, hS₀A, hS₀card, hdisj, hEab, hEcard, hBeq⟩ :=
    sec8B_structure_of_projSp h3 hAF hA81 hfA hf1 hLf hX hxA hxout
  have hAab := hAF.1
  have hAc : ∀ y ∈ A, ∀ y' ∈ A, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  have hAN := le_normalizer_of_projSp h3 hAab hfA hf1 hLf hX
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := Lf)
    Nat.prime_three
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) with hq
  set S' := S₀.map Lf.subtype with hS'
  have hS'card : Nat.card S' = 9 := by
    rw [hS', Subgroup.card_map_of_injective Lf.subtype_injective, hS₀card]
  have hqinj : ∀ s ∈ S₀, ∀ t ∈ S₀, q s = q t → s = t := by
    intro s hs t ht hst
    have h1 : t⁻¹ * s ∈ aschbacherSolvableCore 3 Lf := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hst
      have := (aschbacherSolvableCore 3 Lf).inv_mem hst
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : t⁻¹ * s ∈ S₀ ⊓ aschbacherSolvableCore 3 Lf :=
      ⟨S₀.mul_mem (S₀.inv_mem ht) hs, h1⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  obtain ⟨m, hgm⟩ := hg
  have hgA : g ∈ A := hgm.1
  have hg3 : g ^ 3 = 1 := hAab.2 g hgA
  have hgB : g ∈ sec8B A Lf := by
    refine ⟨hgA, ?_⟩
    show g ∈ Lf ⊔ thetaQuotCentralizer Lf
    rw [mem_sup_thetaQuotCentralizer_iff (hAN hgA)]
    by_contra hout
    have hgout : InducesOuterTheta g Lf := ⟨hAN hgA, hout⟩
    have hX' : Nonempty (Lf ⧸ aschbacherSolvableCore 3 Lf ≃*
        projSp 2 (GaloisField 2 (3 * 1))) := by simpa using hX
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp one_ne_zero hg3 hgout hX'
    have hC720 : Nat.card (barCentralizer (Subgroup.zpowers g) Lf) = 720 := by
      rw [Nat.card_congr ι.toEquiv, card_projSp_two_one]
    have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq (hAN hgA)
      ⟨1, by simpa using hg3⟩
    have hdvd : Nat.card (imageModTheta Lf
        (inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer {g}))) ∣ 720 := by
      rw [himg, ← hC720]
      exact Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)
    rcases hgm.2.2.2 with ⟨k, hk, -, hRee, -⟩ | ⟨-, ⟨hL2⟩⟩
    · exact not_nonempty_reeF4_of_projSp hX k hk hRee
    · rw [Nat.card_congr hL2.toEquiv, card_projSL_two (by have := hgm.2.2.1; omega)] at hdvd
      exact not_dvd_seven_twenty hgm.2.2.1 hdvd
  have hcommfS : ∀ z ∈ Subgroup.zpowers f, ∀ s ∈ S', z * s = s * z := by
    intro z hz s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact hAc _ (A.zpow_mem hfA k) _ (hS₀A hs)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommfS
  have hgdec : g ∈ ((Subgroup.zpowers f ⊔ S' : Subgroup G) : Set G) := by
    rw [← hBeq]
    exact hgB
  rw [hset] at hgdec
  obtain ⟨z, hz, y, hyS, hzy⟩ := hgdec
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hfB : Subgroup.zpowers f ≤ sec8B A Lf := hBeq ▸ le_sup_left
  set K := inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer ({g} : Set G)) with hK
  have hKL : K ≤ Lf :=
    (Subgroup.map_subtype_le _).trans (inf_le_left : Lf ⊓ Subgroup.centralizer {g} ≤ Lf)
  have hyLf : y ∈ Lf := Subgroup.map_subtype_le S₀ hyS
  have hLC : Lf ⊓ Subgroup.centralizer ({g} : Set G) =
      Lf ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hl, hlg⟩
      refine ⟨hl, ?_⟩
      have hlf : l * f = f * l := Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_mem_thetaComponentsAt_three hLf hl)
      have hlfi : l * f ^ i = f ^ i * l := (Commute.zpow_right (show Commute l f from hlf) i).eq
      rw [← hzy] at hlg
      calc l * y = (f ^ i)⁻¹ * (f ^ i * (l * y)) := by group
        _ = (f ^ i)⁻¹ * ((l * f ^ i) * y) := by rw [hlfi]; group
        _ = (f ^ i)⁻¹ * (l * (f ^ i * y)) := by group
        _ = (f ^ i)⁻¹ * (f ^ i * y * l) := by rw [hlg]
        _ = y * l := by group
    · rintro ⟨hl, hly⟩
      refine ⟨hl, ?_⟩
      have hlf : l * f = f * l := Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_mem_thetaComponentsAt_three hLf hl)
      have hlfi : l * f ^ i = f ^ i * l := (Commute.zpow_right (show Commute l f from hlf) i).eq
      rw [← hzy]
      calc l * (f ^ i * y) = f ^ i * (l * y) := by rw [← mul_assoc, hlfi, mul_assoc]
        _ = f ^ i * (y * l) := by rw [hly]
        _ = f ^ i * y * l := by group
  apply le_antisymm
  ·
    rw [hBeq]
    have hfcl : f ∈ Subgroup.closure ({f, g} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hgcl : g ∈ Subgroup.closure ({f, g} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    refine sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_left hfcl)) ?_
    have hycl : y ∈ Subgroup.closure ({f, g} : Set G) := by
      have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hfcl i)) hgcl
      have h2 : (f ^ i)⁻¹ * g = y := by rw [← hzy]; group
      rwa [h2] at h1
    by_cases hy1 : y = 1
    ·
      have hKeq : K = Lf := by
        rw [hK, hLC, hy1]
        have hLC1 : Lf ⊓ Subgroup.centralizer ({1} : Set G) = Lf := by
          rw [inf_eq_left]
          intro l _
          exact Subgroup.mem_centralizer_singleton_iff.mpr (by group)
        rw [hLC1]
        exact CFSG.RankThree.inSubgroup_perfectResidual_of_isPerfect
          (CFSG.RankThree.PartOne.isPerfect_of_mem_thetaComponentsAt hLf)
      intro s hs
      refine Subgroup.mem_sup_right ⟨hS₀A hs, ?_⟩
      rw [hKeq]
      exact Subgroup.map_subtype_le S₀ hs
    ·
      obtain ⟨y₀, hy₀, rfl⟩ := hyS
      set yb := q y₀ with hyb
      have hyb1 : yb ≠ 1 := by
        intro h
        apply hy1
        have := hqinj y₀ hy₀ 1 S₀.one_mem (by rw [← hyb, h, map_one])
        rw [this]
        rfl
      have hybE : yb ∈ S₀.map q := ⟨y₀, hy₀, rfl⟩
      have hyb3 : yb ^ 3 = 1 := hEab.2 _ hybE
      have hEC : S₀.map q ≤ Subgroup.centralizer {yb} := by
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨w, hw⟩ ⟨yb, hybE⟩)
      set ψ : StatedSp 2 (GaloisField 2 3) ≃* (Lf ⧸ aschbacherSolvableCore 3 Lf) :=
        (KFacts.statedSpEquivProjSpOfCharTwo _).trans hX.some.symm with hψ
      have hF4 : 4 ≤ Nat.card (GaloisField 2 3) := by
        rw [GaloisField.card 2 3 (by norm_num)]
        norm_num
      have hcard3 := KFacts.card_inf_perfectResidual_eq_three hF4 ψ hyb3 hyb1 hEC hEab.2 hEcard
        hybE
      have hne : (S₀.map q ⊓ inSubgroup perfectResidual (Subgroup.centralizer {yb}) :
          Subgroup (Lf ⧸ aschbacherSolvableCore 3 Lf)) ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard3
        omega
      obtain ⟨⟨db, hdbmem⟩, hdb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have hdb1' : db ≠ 1 := fun h => hdb1 (Subtype.ext h)
      have hdbC := hdbmem.2
      obtain ⟨d₀, hd₀, hd₀q⟩ := hdbmem.1
      have hdby : db ∉ Subgroup.zpowers yb := by
        intro hmem
        have hdb3 : db ^ 3 = 1 := hEab.2 _ hdbmem.1
        have hord : orderOf db = 3 := orderOf_eq_prime hdb3 hdb1'
        have hordy : orderOf yb = 3 := orderOf_eq_prime hyb3 hyb1
        have heq : Subgroup.zpowers db = Subgroup.zpowers yb :=
          Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hmem)
            (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordy])
        have hyC : yb ∈ inSubgroup perfectResidual (Subgroup.centralizer {yb}) := by
          have : yb ∈ Subgroup.zpowers db := heq ▸ Subgroup.mem_zpowers yb
          exact (Subgroup.zpowers_le.mpr hdbC) this
        exact KFacts.not_mem_perfectResidual_centralizer hF4 ψ hyb3 hyb1 hyC
      have hyA : (y₀ : G) ∈ A := hS₀A ⟨y₀, hy₀, rfl⟩
      have hdA : (d₀ : G) ∈ A := hS₀A ⟨d₀, hd₀, rfl⟩
      have hbar := barCentralizer_zpowers_eq_centralizer y₀.2
      have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq (hAN hyA)
        ⟨1, by simpa using hAab.2 _ hyA⟩
      have hdbimg : db ∈ imageModTheta Lf
          (inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer {(y₀ : G)})) := by
        rw [himg, hbar]
        exact hdbC
      obtain ⟨k₀, hk₀, hk₀q⟩ := hdbimg
      have ht₀ : k₀⁻¹ * d₀ ∈ aschbacherSolvableCore 3 Lf := by
        have h1 : q k₀ = q d₀ := hk₀q.trans hd₀q.symm
        rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
        exact h1
      have htcop : Nat.Coprime (orderOf ((k₀⁻¹ * d₀ : Lf) : G)) 3 := by
        rw [Subgroup.orderOf_coe]
        have hdvd := Subgroup.orderOf_dvd_natCard _ ht₀
        exact Nat.Coprime.coprime_dvd_left hdvd
          (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3))
      have hdN : (d₀ : G) ∈ Subgroup.normalizer
          (inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer {(y₀ : G)}) : Set G) :=
        mem_normalizer_inSubgroup_perfectResidual
          (mem_normalizer_inf_centralizer (hAN hdA) (hAc _ hdA _ hyA))
      have hd3 : (d₀ : G) ^ 3 = 1 := hAab.2 _ hdA
      have hdK : (d₀ : G) ∈ inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer {(y₀ : G)}) :=
        mem_of_mul_mem_of_coprime hd3 hdN (Subgroup.mem_subgroupOf.mp hk₀)
          (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group) htcop
      have hdy : (d₀ : G) ∉ Subgroup.zpowers (y₀ : G) := by
        rintro ⟨j, hj⟩
        apply hdby
        refine ⟨j, ?_⟩
        have hj' : y₀ ^ j = d₀ := Subtype.ext (by simpa using hj)
        show yb ^ j = db
        rw [hyb, ← map_zpow, hj', hd₀q]
      have hord3 : ∀ w ∈ A, w ≠ 1 → orderOf w = 3 := fun w hw hw1 =>
        orderOf_eq_prime (hAab.2 w hw) hw1
      have hd1 : (d₀ : G) ≠ 1 := fun h => hdy (h ▸ Subgroup.one_mem _)
      have hy1' : (y₀ : G) ≠ 1 := hy1
      have hinf : Subgroup.zpowers (y₀ : G) ⊓ Subgroup.zpowers (d₀ : G) = ⊥ := by
        have hcard : Nat.card (Subgroup.zpowers (d₀ : G)) = 3 := by
          rw [Nat.card_zpowers, hord3 _ hdA hd1]
        have : Fact (Nat.card (Subgroup.zpowers (d₀ : G))).Prime := ⟨by rw [hcard]; norm_num⟩
        rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Subgroup.zpowers (y₀ : G) ⊓
            Subgroup.zpowers (d₀ : G)).subgroupOf (Subgroup.zpowers (d₀ : G))) with h | h
        · rw [Subgroup.subgroupOf_eq_bot] at h
          have h' := disjoint_iff.1 h
          rwa [inf_assoc, inf_idem] at h'
        · exfalso
          have hmem : (⟨(d₀ : G), Subgroup.mem_zpowers _⟩ : Subgroup.zpowers (d₀ : G)) ∈
              (Subgroup.zpowers (y₀ : G) ⊓ Subgroup.zpowers (d₀ : G)).subgroupOf
                (Subgroup.zpowers (d₀ : G)) := by
            rw [h]
            exact Subgroup.mem_top _
          exact hdy (Subgroup.mem_subgroupOf.1 hmem).1
      have hcommyd : ∀ u ∈ Subgroup.zpowers (y₀ : G), ∀ v ∈ Subgroup.zpowers (d₀ : G),
          u * v = v * u := by
        intro u hu v hv
        exact hAc u ((Subgroup.zpowers_le (H := A)).mpr hyA hu) v
          ((Subgroup.zpowers_le (H := A)).mpr hdA hv)
      obtain ⟨hcardyd, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommyd
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
        hord3 _ hyA hy1', hord3 _ hdA hd1] at hcardyd
      have hydS : Subgroup.zpowers (y₀ : G) ⊔ Subgroup.zpowers (d₀ : G) ≤ S' :=
        sup_le ((Subgroup.zpowers_le).mpr ⟨y₀, hy₀, rfl⟩)
          ((Subgroup.zpowers_le).mpr ⟨d₀, hd₀, rfl⟩)
      have hSeq : Subgroup.zpowers (y₀ : G) ⊔ Subgroup.zpowers (d₀ : G) = S' :=
        Subgroup.eq_of_le_of_card_ge hydS (by rw [hS'card, hcardyd])
      rw [← hSeq]
      refine sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_left hycl))
        ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_right ⟨hdA, ?_⟩))
      rw [hK, hLC]
      exact hdK
  ·
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact hfB (Subgroup.mem_zpowers _)
      · exact hgB
    · rintro w ⟨hwA, hwK⟩
      exact ⟨hwA, Subgroup.mem_sup_left (hKL hwK)⟩

end Final
end CFSG.RankThree.PartTwo.Sec8
end

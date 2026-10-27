public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

open scoped commutatorElement

theorem asch1413For_of_red {S : ∀ (L : Type) [Group L], Prop}
    (hS : ∀ (L : Type) [Group L], S L → IsSimpleGroup L ∧ ∃ a b : L, a * b ≠ b * a)
    (h : Asch1413RedFor S) : Asch1413For S := by
  intro Q _ _ V _ _ hV ρ hρ L A hL hSL hA hAe hq
  subst hL
  obtain ⟨hs, hnab⟩ := hS ↥(genFittingFStar Q) hSL
  haveI : IsSimpleGroup ↥(genFittingFStar Q) := hs
  have hLn : (genFittingFStar Q).Normal := CFSG.ClassicalInvolution.genFittingFStar_normal Q
  have hcent : Subgroup.centralizer (genFittingFStar Q : Set Q) = ⊥ :=
    CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab
  have hperfect : Group.IsPerfect ↥(genFittingFStar Q) :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun hc =>
      let ⟨a, b, hab⟩ := hnab
      hab (isMulCommutative_iff.mp hc a b)
  have hperf : ⁅genFittingFStar Q, genFittingFStar Q⁆ = genFittingFStar Q :=
    Subgroup.commutator_eq_self
  let G : Subgroup (MulAut V) := ρ.range
  let L' : Subgroup (MulAut V) := (genFittingFStar Q).map ρ
  have hLG : L' ≤ G := Subgroup.map_le_range ρ (genFittingFStar Q)
  have hnorm : ∀ g ∈ G, ∀ l ∈ L', g * l * g⁻¹ ∈ L' := by
    intro g hg l hl
    obtain ⟨q, rfl⟩ := hg
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    simpa only [map_mul, map_inv] using
      Subgroup.mem_map_of_mem ρ (hLn.conj_mem l₀ hl₀ q)
  have hperf' : ⁅L', L'⁆ = L' := by
    have hmap := Subgroup.map_commutator (H₁ := genFittingFStar Q)
      (H₂ := genFittingFStar Q) ρ
    rw [hperf] at hmap
    exact hmap.symm
  have hL' : L' ≠ ⊥ := by
    intro hbot
    have hbot' : genFittingFStar Q = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := genFittingFStar Q) hρ).mp hbot
    haveI : Nontrivial ↥(genFittingFStar Q) := hs.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot (genFittingFStar Q)).mp inferInstance hbot'
  obtain ⟨W, hGW, hWnon, hWmem⟩ :=
    Asch6.exists_quot_fixV_eq_bot (V := V) hLG hnorm hperf' hL'
  let ρ' : Q →* MulAut (V ⧸ W) :=
    (quotHom W).comp (ρ.codRestrict (stabSub W) (fun q => hGW ⟨q, rfl⟩))
  have hρ'_apply : ∀ (q : Q) (v : V),
      ρ' q (QuotientGroup.mk v) = QuotientGroup.mk (ρ q v) := by
    intro q v
    exact quotHom_mk W (ρ.codRestrict (stabSub W) (fun q => hGW ⟨q, rfl⟩) q) v
  have hNnormal : ρ'.ker.Normal := MonoidHom.normal_ker ρ'
  have hNLbot : ρ'.ker.subgroupOf (genFittingFStar Q) = ⊥ := by
    haveI hNLnormal : (ρ'.ker.subgroupOf (genFittingFStar Q)).Normal :=
      hNnormal.subgroupOf (genFittingFStar Q)
    rcases hs.eq_bot_or_eq_top_of_normal (ρ'.ker.subgroupOf (genFittingFStar Q)) with h | h
    · exact h
    · exfalso
      apply hWnon
      intro x hx
      obtain ⟨l, hl, rfl⟩ := hx
      have hlN : (⟨l, hl⟩ : ↥(genFittingFStar Q)) ∈
          ρ'.ker.subgroupOf (genFittingFStar Q) := by
        rw [h]; exact Subgroup.mem_top _
      rw [Subgroup.mem_subgroupOf] at hlN
      have hk : ρ' l = 1 := MonoidHom.mem_ker.mp hlN
      have hk' : quotHom W (ρ.codRestrict (stabSub W)
          (fun q => hGW ⟨q, rfl⟩) l) = 1 := hk
      rw [← MonoidHom.mem_ker, ker_quotHom] at hk'
      rw [Subgroup.mem_subgroupOf] at hk'
      simpa using hk'
  have hρ' : Function.Injective ρ' := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro n hn
    have hcent_mem : n ∈ Subgroup.centralizer (genFittingFStar Q : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmemL : ⁅n, l⁆ ∈ genFittingFStar Q := by
        rw [commutatorElement_def]
        exact (genFittingFStar Q).mul_mem (hLn.conj_mem l hl n)
          ((genFittingFStar Q).inv_mem hl)
      have hmemN : ⁅n, l⁆ ∈ ρ'.ker := by
        rw [commutatorElement_def]
        have hconj : l * n * l⁻¹ ∈ ρ'.ker := (MonoidHom.normal_ker ρ').conj_mem n hn l
        have hprod : n * (l * n * l⁻¹)⁻¹ ∈ ρ'.ker :=
          ρ'.ker.mul_mem hn (ρ'.ker.inv_mem hconj)
        convert hprod using 1
        group
      let c : ↥(genFittingFStar Q) := ⟨⁅n, l⁆, hmemL⟩
      have hc : c ∈ ρ'.ker.subgroupOf (genFittingFStar Q) := by
        rw [Subgroup.mem_subgroupOf]
        exact hmemN
      rw [hNLbot, Subgroup.mem_bot] at hc
      have hc1 : (c : Q) = 1 := congrArg Subtype.val hc
      rw [commutatorElement_eq_one_iff_mul_comm] at hc1
      exact hc1.symm
    rw [hcent, Subgroup.mem_bot] at hcent_mem
    exact hcent_mem
  have hV' : ∀ v : V ⧸ W, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, hV x]
      rfl
  have hq' : IsQuadraticOn ρ' A := by
    intro a ha b hb v
    induction v using QuotientGroup.induction_on with
    | H x =>
      have h1 : (ρ' a (QuotientGroup.mk x) * (QuotientGroup.mk x)⁻¹ : V ⧸ W) =
          QuotientGroup.mk (ρ a x * x⁻¹) := by
        rw [hρ'_apply a x, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rw [h1, hρ'_apply b (ρ a x * x⁻¹), hq a ha b hb x]
  have hC' : ∀ v : V ⧸ W, (∀ l ∈ genFittingFStar Q, ρ' l v = v) → v = 1 := by
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    have hxW : x ∈ W := by
      apply hWmem x
      intro l hl
      obtain ⟨l₀, hl₀, rfl⟩ := hl
      have h := hv l₀ hl₀
      rw [hρ'_apply l₀ x] at h
      exact (mk_eq_mk_iff (ρ l₀ x) x).mp h
    rw [QuotientGroup.eq_one_iff]
    exact hxW
  exact h Q (V ⧸ W) hV' ρ' hρ' (genFittingFStar Q) A rfl hSL hA hAe hq' hC'

end CFSG.LocalAnalysis.WeakClosure81
end

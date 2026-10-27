public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.UniquenessMaximal

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l73_prod_odd (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {J : Subgroup G}
    (hB : IsSStarMax 3 B x L) {a b : G} (hess : IsEssential 3 B a) (hd : dLevel G 3 = 3)
    {M K : Subgroup G} (hP : L73Prod b a M K J) (hlev : fullCoverLevel 3 (PQuot 3 M) = 3) :
    Odd (Nat.card ↥(⁅K, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))⁆ : Subgroup G)) := by
  classical
  obtain ⟨hM, -, -, hKeq, hba, -, -, -⟩ := hP
  have hST : IsSTriple 3 B a M := ⟨IsSStarMax.bmax hB, hess, hM⟩
  have hS0 : IsS0 3 B a M :=
    ⟨hST, (tripleLevel_eq_three (le_three_of_isSTriple hST hd).1 hlev).trans hd.symm⟩
  have hodd : Odd (Nat.card ↥(⁅M, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))⁆ : Subgroup G)) :=
    hc.stage4.1 B a M hS0
  set C := Subgroup.centralizer ({a} : Set G) with hCdef
  set O := GLAPPrimeCoreOf 3 C with hOdef
  have hMC : M ≤ C := hM.1
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 C
  have hnormO : ∀ x ∈ C, ∀ o ∈ O, x * o * x⁻¹ ∈ O := fun x hx o ho =>
    (Subgroup.mem_normalizer_iff.1 (hCO hx) o).1 ho
  have hOn : ∀ g ∈ C, GLBConj g O = O := fun g hg => mem_normalizer_iff_gLBConj_eq.1 (hCO hg)
  let f : C → Subgroup G := fun c => ⁅GLBConj (c : G) M, O⁆
  have hGC1 : ∀ c : C, GLBConj (c : G) M ≤ C := fun c => y5x_glbConj_le c.2 hMC
  have hfle : ∀ c : C, f c ≤ O := fun c => by
    refine Subgroup.commutator_le.2 fun x hx o ho => ?_
    rw [commutatorElement_def]
    exact O.mul_mem (hnormO x (hGC1 c hx) o ho) (O.inv_mem ho)
  have hfn : ∀ c : C, O ≤ Subgroup.normalizer ((f c : Subgroup G) : Set G) := fun c =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hfle c)).1
      (normal_subgroupOf_commutator ((hGC1 c).trans hCO))
  have hfodd : ∀ c : C, Odd (Nat.card ↥(f c)) := fun c => by
    show Odd (Nat.card ↥(⁅GLBConj (c : G) M, O⁆ : Subgroup G))
    rw [y5x_glbConj_commutator M O (c : G) (hOn c c.2), y5x_card_glbConj]
    exact hodd
  have hRodd : Odd (Nat.card ↥(⨆ c : C, f c)) :=
    y5x_odd_iSup_of_normalized f hfle hfn hfodd
  set R : Subgroup G := ⨆ c : C, f c with hRdef
  have hRle : R ≤ O := iSup_le hfle
  have hmem : ∀ g ∈ C, ⁅GLBConj g M, O⁆ ≤ R := fun g hg => le_iSup f ⟨g, hg⟩
  have hRC : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hc
    have hOφ : O.map (MulAut.conj c).toMonoidHom = O := by
      have h1 := y5x_map_conj_glbConj c 1 O
      rw [gLBConj_one, one_mul] at h1
      rw [h1]
      exact hOn c⁻¹ (C.inv_mem hc)
    have hmap : R.map (MulAut.conj c).toMonoidHom ≤ R := by
      rw [hRdef, Subgroup.map_iSup]
      refine iSup_le fun i => ?_
      show (⁅GLBConj (i : G) M, O⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom ≤ R
      rw [Subgroup.map_commutator, y5x_map_conj_glbConj, hOφ]
      exact hmem _ (C.mul_mem i.2 (C.inv_mem hc))
    intro r hr
    exact hmap (Subgroup.mem_map.2 ⟨r, hr, rfl⟩)
  let S : Subgroup G :=
    { carrier := {k | k ∈ C ∧ ∀ o ∈ O, ⁅k, o⁆ ∈ R}
      mul_mem' := by
        rintro k k' ⟨hk, hkO⟩ ⟨hk', hk'O⟩
        refine ⟨C.mul_mem hk hk', fun o ho => ?_⟩
        have e : ⁅k * k', o⁆ = k * ⁅k', o⁆ * k⁻¹ * ⁅k, o⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact R.mul_mem (hRC k hk _ (hk'O o ho)) (hkO o ho)
      one_mem' := ⟨C.one_mem, fun o _ => by simp⟩
      inv_mem' := by
        rintro k ⟨hk, hkO⟩
        refine ⟨C.inv_mem hk, fun o ho => ?_⟩
        have e : ⁅k⁻¹, o⁆ = k⁻¹ * (⁅k, o⁆)⁻¹ * k⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hRC k⁻¹ (C.inv_mem hk) _ (R.inv_mem (hkO o ho)) }
  have hS_mem : ∀ k, k ∈ S ↔ k ∈ C ∧ ∀ o ∈ O, ⁅k, o⁆ ∈ R := fun k => Iff.rfl
  have hMS : M ≤ S := fun m hm => by
    rw [hS_mem]
    refine ⟨hMC hm, fun o ho => ?_⟩
    have h1 : (⁅M, O⁆ : Subgroup G) ≤ R := by
      have h2 := hmem 1 C.one_mem
      rwa [gLBConj_one] at h2
    exact h1 (Subgroup.commutator_mem_commutator hm ho)
  have hbMS : GLBConj b M ≤ S := fun y hy => by
    rw [hS_mem]
    refine ⟨y5x_glbConj_le hba hMC hy, fun o ho => ?_⟩
    exact hmem b hba (Subgroup.commutator_mem_commutator hy ho)
  have hbbMS : GLBConj b (GLBConj b M) ≤ S := fun y hy => by
    rw [hS_mem]
    refine ⟨y5x_glbConj_le hba (y5x_glbConj_le hba hMC) hy, fun o ho => ?_⟩
    have h2 : (⁅GLBConj b (GLBConj b M), O⁆ : Subgroup G) ≤ R := by
      rw [gLBConj_gLBConj]
      exact hmem (b * b) (C.mul_mem hba hba)
    exact h2 (Subgroup.commutator_mem_commutator hy ho)
  have hKS : K ≤ S := by
    rw [hKeq]
    exact sup_le (sup_le hMS hbMS) hbbMS
  have hcomm : ⁅K, O⁆ ≤ R :=
    Subgroup.commutator_le.2 fun k hk o ho => ((hS_mem k).1 (hKS hk)).2 o ho
  exact Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le hcomm)

end CFSG.LocalAnalysis.GLTheoremA
end

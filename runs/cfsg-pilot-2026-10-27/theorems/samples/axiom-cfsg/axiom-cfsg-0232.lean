public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin

open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim78

open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

theorem mem_of_isOrthModule_of_commutator_mem_beta
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (E : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hE hN))
    {v : G} (hvK : ∀ k ∈ kOf V H, k * v = v * k)
    (hvP : ∀ p ∈ Pc M V, ⁅p, v⁆ ∈ E)
    {y : G} (hy : y ∈ conjSubgroup h₀ (Pc M V)) (hyK : y ∉ kOf V H)
    (hvy : ⁅y, v⁆ ∈ E) :
    v ∈ E := by
  classical
  have hyH : y ∈ H := by
    have hle : conjSubgroup h₀ (Pc M V) ≤ H := by rw [hH]; exact le_sup_right
    exact hle hy
  let H₁ : Subgroup G := CFSG.GroupTheory.commMemSubgroup H E hN v
  have hH₁le : H₁ ≤ H := fun g hg => hg.1
  have hP_le : Pc M V ≤ H₁ := by
    intro p hp
    exact ⟨hPH hp, hvP p hp⟩
  have hK_le : kOf V H ≤ H₁ := by
    intro k hk
    refine ⟨kOf_le V H hk, ?_⟩
    have hcomm : k * v = v * k := hvK k hk
    have h1 : ⁅k, v⁆ = 1 := by
      rw [commutatorElement_def]
      rw [show k * v = v * k from hcomm]
      group
    rw [h1]
    exact E.one_mem
  have hy_mem : y ∈ H₁ := ⟨hyH, hvy⟩
  have himg_top : imgK V H H₁ = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← sup_imgK_conj_eq_top_of_sl2 h hPH hVH hH hnM ψ
      (y := piK V H ⟨y, hyH⟩) ?_ ?_]
    · refine sup_le (imgK_mono hP_le) ?_
      have hPy_le : conjSubgroup y (Pc M V) ≤ H₁ := by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
        exact H₁.mul_mem (H₁.mul_mem hy_mem (hP_le hp)) (H₁.inv_mem hy_mem)
      rw [← imgK_conjSubgroup hyH hPH]
      exact imgK_mono hPy_le
    · exact (mem_imgK_iff).mpr ⟨⟨y, hyH⟩, hy, rfl⟩
    · intro h1
      exact hyK ((piK_eq_one_iff _).mp h1)
  have hH₁_eq : H₁ = H := by
    have h1 := (imgK_eq_iff_sup_kOf_eq (V := V) (H := H)
      hH₁le (le_refl H)).mp ?_
    · rwa [sup_eq_left.mpr hK_le, sup_eq_left.mpr (kOf_le V H)] at h1
    · rw [himg_top, imgK_self]
  have hvH : ∀ g ∈ H, ⁅g, v⁆ ∈ E := by
    intro g hg
    exact (hH₁_eq.symm ▸ hg : g ∈ H₁).2
  exact mem_of_isOrthModule_of_commutator_mem h hPH hH hnM ψ hl hE hN horth hvK hvH

end RootHyp
end CFSG.RankThree.GF2n.Tim81
end

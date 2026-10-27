public section

namespace CFSG.RankThree.PartOne.KCSymplectic

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven CFSG.ClassicalGroups.Alternating

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Block

variable {r : ℕ} {K : Type} [Field K]

variable {x : StatedSp r K} {h : primaryFactors (spEnd x)} {p m : ℕ}

theorem TorusBlock.witness_odd (T : TorusBlock x h p m) [Finite K] {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) (φ : Y →* StatedProj (StatedSp r K))
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ m ∧ m ≤ localRank p G := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h2E : (2 : AdjoinRoot (h : K[X])) ≠ 0 := by
    intro h0
    apply h2
    apply (algebraMap K (AdjoinRoot (h : K[X]))).injective
    rw [map_ofNat, map_zero]
    exact h0
  obtain ⟨g, hψg, hg2, hgc⟩ := exists_sign_lift T.basis T.lam T.lam_pow T.ψ T.injective T.diag i₀
    (T.sign i₀)
  refine block_torus_central_cover_witness T.basis Y (proj r K) φ hφ hker hp hp2 T.lam_pow
    T.lam_order T.ψ T.injective T.diag T.perm
    (fun g _ hg1 hgp => eq_one_of_proj_eq_one_of_pow_eq_one hr hp2 hp hg1 hgp)
    ⊤ (k := m) (le_of_eq (by rw [Subgroup.card_top, card_multiplicative_fin_zmod]))
    (z := (g : StatedSp r K)) hg2 ?_ (fun a _ => hgc a)
  intro hz1
  obtain ⟨c, hc⟩ := exists_smul_of_proj_eq_one hz1
  refine sign_not_scalar T.basis h2E hi (algebraMap K _ c) (fun w => ?_)
  apply Subtype.ext
  rw [← hψg, T.act g w, hc, coe_algebraMap_smul_primaryComponent]

end Block
end CFSG.RankThree.PartOne.KCSymplectic
end

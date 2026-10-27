public section

namespace CFSG.Semidihedral.AllPrime

noncomputable section

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

open CFSG.Semidihedral.EscapingLocalEigensubgroups

open CFSG.ABGTheoremB CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.AllPrime.QDTI

open CFSG.Wreathed.OriginalAllPrime.TIFacts CFSG.QuasiDihedralFusion

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
theorem frontier_TI_F₀_omega
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (_hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (_ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (frontier_F₀_eq_T : (frontierSetting S fS t p f).D ⊓
      Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) =
        (frontierSetting S fS t p f).T) :
    ∀ g ∈ (frontierSetting S fS t p f).F₀, g ^ 2 = 1 → g ∈ (frontierSetting S fS t p f).T := by
  intro g hg _
  change g ∈ (frontierSetting S fS t p f).D ⊓
    Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) at hg
  rwa [frontier_F₀_eq_T] at hg

end
end CFSG.Semidihedral.AllPrime
end

public section

namespace CFSG.RankThree.CentralLiftSO.Sp

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt CFSG.RankThree.CentralLift

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E] [Finite k] [Finite E]
  {π : E →* StatedSp r k}

section Kernel

variable (hS : LargeHyp π)

include hS

theorem injective_pi_comp : Function.Injective (π.comp (liftWeyl π).subtype) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hn' : π n = 1 := hn
  have hw : weylHom hS n = 1 := by
    apply Subtype.ext
    refine weylHom_eq hS ?_
    change IsLinePerm 1 (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
    rw [hn']
    exact isLinePerm_one
  have hH : (n : E) ∈ liftTorus π := Subgroup.mem_subgroupOf.1 (ker_weylHom_le hS hw)
  obtain ⟨t, ht⟩ := (range_thetaHom hS).ge hH
  have h1 : torusHom t = 1 := by
    rw [← comp_thetaHom hS, MonoidHom.comp_apply, ht]
    exact hn'
  have ht1 : t = 1 := torusHom_injective (h1.trans (map_one _).symm)
  apply Subtype.ext
  rw [← ht, ht1, map_one]
  rfl

end Kernel
end CFSG.RankThree.CentralLiftSO.Sp
end

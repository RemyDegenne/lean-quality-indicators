public section

namespace CFSG.SectionRank.OddCover

open scoped commutatorElement Pointwise

section Monomial

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem six_mul_le_card_torus3_sup [Finite K] (M : Subgroup Kˣ) :
    6 * Nat.card M ^ 2 ≤
      Nat.card ↥(torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K))) := by
  set N := torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K))
  have hs01 : (s01GL : GL (Fin 3) K) ∈ N :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hs12 : (s12GL : GL (Fin 3) K) ∈ N :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hle : torus3 M ⊔ Subgroup.zpowers cycGL ≤ N := by
    refine sup_le le_sup_left ?_
    rw [Subgroup.zpowers_le, ← s01GL_mul_s12GL]
    exact N.mul_mem hs01 hs12
  have hlt : torus3 M ⊔ Subgroup.zpowers cycGL < N :=
    lt_of_le_of_ne hle fun h => s01GL_not_mem_torus3_sup_cyc M (h ▸ hs01)
  have hdvd := Subgroup.card_dvd_of_le hle
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [card_torus3_sup_cyc] at hdvd hcard
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hcard ⊢
  have hk2 : 2 ≤ k := by
    by_contra hk2
    interval_cases k <;> omega
  nlinarith

end Monomial
end CFSG.SectionRank.OddCover
end

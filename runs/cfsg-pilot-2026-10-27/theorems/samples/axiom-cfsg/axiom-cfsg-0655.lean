public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory

open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.Chevalley

open CFSG.LieType.Chevalley

open scoped Pointwise

theorem even_E6_noninner_actual_component_local_core_product_centralizes {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {f : ℕ} (hf : 1 ≤ f)
    (hT : ChevalleyExceptionalModel (L ⧸ center L) .E6 2 f)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hnon : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
        Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G) ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hT.2
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  have hcore : LocalCoreTrivialOn p fun α : MulAut (adjointGroup .E6 K) =>
      α ∉ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hK Θ hΘ hp hp3 B
        hB α hα hαp).2.2
  exact noninner_component_local_core_product_centralizes hp (by omega) hE hEcard ht ht1 hL hEL
    hSL e hcore hnon

end CFSG.RankThree.Chevalley
end

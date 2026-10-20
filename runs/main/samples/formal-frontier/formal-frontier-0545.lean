@[expose] public section

universe u v w

namespace Finsupp

theorem mapDomain_degree_support_hasLeftInverse_iff (M : Type w) [AddCommMonoid M] :
    Function.HasLeftInverse
        (Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) :
          ((Fin 2 →₀ ℕ) →₀ M) → ((ℕ × ℕ) →₀ M)) ↔
      Subsingleton M := by
  have hcollision :
      ¬ Function.Injective (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) := by
    intro h
    have hsingle :
        (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) =
          Finsupp.single (1 : Fin 2) 1 := by
      apply h
      simp only [Finsupp.degree_single,
        Finsupp.support_single (0 : Fin 2) Nat.one_ne_zero,
        Finsupp.support_single (1 : Fin 2) Nat.one_ne_zero, Finset.card_singleton]
    have hindex : (0 : Fin 2) = 1 :=
      Finsupp.single_left_injective Nat.one_ne_zero hsingle
    exact Nat.zero_ne_one (congrArg Fin.val hindex)
  rw [← Function.injective_iff_hasLeftInverse, mapDomain_injective_iff]
  simp only [hcollision, false_or]

end Finsupp
end

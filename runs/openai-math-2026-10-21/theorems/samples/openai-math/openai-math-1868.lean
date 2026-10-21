namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem exists_regular_onecut_sum_and_local_counts [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i < n, ((J i).colon {f i}).IsPrime) ∧
      (((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) =
        ∑ i ∈ Finset.range n, if (J i).colon {f i} ∈ minimalPrimes A then
          ((Module.length A (A ⧸ ((J i).colon {f i} ⊔ Ideal.span {x}))).toNat : ℤ) else 0) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  classical
  obtain ⟨n, J, f, hm, h0, hn, hs, hcounts⟩ :=
    exists_cyclic_filtration_all_local_counts (A := A)
  refine ⟨n, J, f, (fun i hi => (hs i hi).1), ?_, hcounts⟩
  have he := cutEuler_filtration J f x n (fun i hi => (hs i hi).2)
    (regular_cut_length_ne_top x hx) (regular_colon_length_ne_top x hx)
  rw [h0, hn, cutEuler_top, add_zero, cutEuler_bot_regular x hx] at he
  refine he.trans (Finset.sum_congr rfl ?_)
  intro i hi
  let : ((J i).colon {f i}).IsPrime := (hs i (Finset.mem_range.mp hi)).1
  exact cutEuler_prime_regular x hx ((J i).colon {f i})

end PiExponentJets.W28.LocalIntersection
end OAI

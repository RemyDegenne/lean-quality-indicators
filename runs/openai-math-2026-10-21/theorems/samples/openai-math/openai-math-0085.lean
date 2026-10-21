namespace OAI

namespace Ostmann

open scoped Classical BigOperators

theorem initialWordPrior_atomIntervals_equiv {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole)
    (k m j : ℕ) (s : C → ℕ) (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (P : Finset ℕ) (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (lo hi : (Σ c, Fin (s c)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → lo i ≤ q ∧ q ≤ hi i)
    (x : (Σ v : Bool × Option C, Fin (initialWordSize k s v.2)) → P)
    (hx : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv k m s cell i)) (x i)) ≠ 0) :
    (∀ r ∈ atomIntervalRanges role
      (initialWordAtomLower j (fun c => ∏ i, lo ⟨c, i⟩))
      (initialWordAtomUpper j (fun c => ∏ i, hi ⟨c, i⟩)) 0,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) ↔
    ∀ r ∈ initialWordBinRanges role j,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) :=
  initialWordAtomIntervals_equiv role j _ _ _
    (initialWordPrior_cell_product_bounds k m s cell P Q R lo hi hcell x hx)

end Ostmann
end OAI

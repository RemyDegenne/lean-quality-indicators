namespace OAI

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

section

variable {I D : Type*} [Fintype I] [Fintype D]

variable (role : I → CopyScheduleRole) (size : I → ℕ)

variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)

variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))

variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)

variable (Q : (Σ i, Fin (size i)) → Finset ℕ)

variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))

variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

omit [Fintype D] in
theorem constituentOriginalMatchedPair_eq
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (d d' : D) (M : ℕ) :
    constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist e d d' M =
      ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
        ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
        ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
          constituentCharacterCoefficient role size χ κ pivot n P hP Q childBound pivotBound ranges
            leaf hist u M (l, d) *
          conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q childBound pivotBound ranges
            leaf hist u M (l ∘ e.symm, d')) := by
  unfold constituentOriginalMatchedPair
  simp_rw [mul_assoc]
  have hsplit := sum_split_prime_prior (H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)
    (Y := CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) P
    (Sum.elim (fun h => Q (copyScheduleOrigin n h.val)) (fun y => Q (copyScheduleOrigin n y.val)))
    (fun x => ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val))
      (x (.inl (e.symm h))) : ℝ) : ℂ) *
      (constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist
        (fun y => x (.inr y)) M ((fun h => x (.inl h)), d) *
      conj (constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist
        (fun y => x (.inr y)) M ((fun h => x (.inl (e.symm h))), d'))))
  simp only [finite_univ_canonical, Sum.elim_inl, Sum.elim_inr] at hsplit ⊢
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [constituentCharacterCoefficient_factor, constituentCharacterCoefficient_factor]
  simp only [Function.comp_apply, map_mul, Complex.conj_ofReal, finite_univ_canonical]
  dsimp only [Function.comp_def]
  ring

end
end Ostmann
end OAI

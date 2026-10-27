public section

namespace CFSG.Permutation.FinPack

open Equiv

variable {F G H K : Finset (Perm (Fin 6))} {P Q R S : List ℕ}

theorem invol_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) (hH : ∀ σ, σ ∈ H ↔ memK (pc6 σ) R = true)
    {e : ℕ} (he : pc6 1 = e)
    (hc : allK (fun p => !Nat.beq (mulP6 p p) e || memK p Q || memK p R) P = true) :
    ∀ r ∈ F, r * r = 1 → r ∈ G ∨ r ∈ H := by
  intro r hr hrr
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF r).1 hr))
  rw [← he, ← pc6_mul, hrr, Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    ← hG, ← hH] at h
  exact h

end CFSG.Permutation.FinPack
end

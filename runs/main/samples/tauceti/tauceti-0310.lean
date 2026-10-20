public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

section Dominant

variable {R : Type*} [CommRing R] [CharZero R] {n : ℕ}

variable {mu nu : Fin n → R}

theorem IsGlDominantIntegral.antitone_of_eq_natCast_add_const
    (hmu : IsGlDominantIntegral mu) {a : Fin n → ℕ} {c : R}
    (h : mu = fun i => (a i : R) + c) : Antitone a := by
  intro i j hij
  obtain ⟨d, hd⟩ := hmu.exists_natCast_sub_of_le hij
  have hdiff : (a i : R) - (a j : R) = (d : R) := by
    calc
      (a i : R) - (a j : R) = mu i - mu j := by rw [h]; ring
      _ = (d : R) := hd
  have hcast : ((a j + d : ℕ) : R) = (a i : R) := by
    rw [Nat.cast_add]
    calc
      (a j : R) + (d : R) = (d : R) + (a j : R) := add_comm _ _
      _ = (a i : R) := (sub_eq_iff_eq_add.mp hdiff).symm
  exact Nat.le.intro (Nat.cast_injective hcast)

end Dominant
end TauCeti
end

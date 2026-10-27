public section

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral

variable {n : ℕ}

theorem aut_s_coords (hn : 4 ≤ n) (ψ : MulAut (SemidihedralGroup n)) {a : ZMod (modulus n)}
    (ha : a.val % 2 = 1) (har : ψ (r n) = element n (by omega) a 0) :
    ∃ b : ZMod (modulus n), ψ (s n) = element n (by omega) b 1 := by
  obtain ⟨⟨b, e⟩, he⟩ := (coordinateEquiv n (by omega)).symm.surjective (ψ (s n))
  change element n (by omega) b e = ψ (s n) at he
  rcases exponent_cases e with rfl | rfl
  · exfalso
    obtain ⟨u, hu⟩ := isUnit_of_odd a ha
    have hrot := aut_rotation hn ψ har (↑u⁻¹ * b)
    have hab : a * (↑u⁻¹ * b) = b := by
      rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hab, he] at hrot
    have hinj := ψ.injective hrot
    rw [s_eq_element n (by omega), element_eq_iff] at hinj
    exact absurd hinj.2 (by decide)
  · exact ⟨b, he.symm⟩

end CFSG.Semidihedral.FieldFactorOne
end

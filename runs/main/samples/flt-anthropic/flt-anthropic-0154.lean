namespace P2MW.S_CuspidalType_sum_character_mul_character_inv

set_option autoImplicit false

open CuspidalType

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤) :
    ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q) := by
  classical
  haveI : Representation.IsIrreducible ρ :=
    { exists_pair_ne := ⟨⊥, ⊤, fun h => by
        have h' : (⊥ : Submodule K V) = ⊤ := congrArg Subrepresentation.toSubmodule h
        exact bot_ne_top h'⟩
      eq_bot_or_eq_top := fun W => by
        by_cases h : W.toSubmodule = ⊥
        · exact Or.inl (Subrepresentation.toSubmodule_injective h)
        · exact Or.inr (Subrepresentation.toSubmodule_injective (hirr W h)) }
  have hcard : (Nat.card (GL2 q) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  haveI : Invertible (Nat.card (GL2 q) : K) := invertibleOfNonzero hcard
  have h := Representation.char_orthonormal ρ ρ
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at h
  have h2 := congrArg (fun x => (Nat.card (GL2 q) : K) * x) h
  rwa [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at h2

end P2MW.S_CuspidalType_sum_character_mul_character_inv

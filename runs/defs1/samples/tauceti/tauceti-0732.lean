public section

namespace TauCeti

universe u

namespace AddCommGroup

variable (A : Type u) [AddCommGroup A] [Finite A]

/-- A finite abelian group is canonically the direct product of its prime-primary components. -/
noncomputable def primaryDecomposition :
    (∀ p : (Nat.card A).primeFactors, AddCommGroup.primaryComponent A p.1) ≃+ A :=
  AddEquiv.ofBijective (primaryDecompositionHom A) (by
    classical
    let _ := Fintype.ofFinite A
    let _ : ∀ p : (Nat.card A).primeFactors,
        Fintype (AddCommGroup.primaryComponent A p.1) := fun _ ↦ Fintype.ofFinite _
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · rw [primaryDecompositionHom]
      apply AddSubgroup.injective_noncommPiCoprod_of_iSupIndep
      apply AddSubgroup.independent_of_coprime_order (primaryComponents_pairwise_addCommute A)
      rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
      rw [← Nat.card_eq_fintype_card, natCard_primaryComponent A ⟨p, hp⟩,
        ← Nat.card_eq_fintype_card, natCard_primaryComponent A ⟨q, hq⟩]
      exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr (by simpa using hpq)).pow _ _
    · simp only [← Nat.card_eq_fintype_card]
      calc
        Nat.card (∀ p : (Nat.card A).primeFactors,
            AddCommGroup.primaryComponent A p.1) =
            ∏ p : (Nat.card A).primeFactors,
              Nat.card (AddCommGroup.primaryComponent A p.1) := Nat.card_pi
        _ = ∏ p : (Nat.card A).primeFactors,
            p.1 ^ (Nat.card A).factorization p.1 := by
          congr 1 with p
          exact natCard_primaryComponent A p
        _ = ∏ p ∈ (Nat.card A).primeFactors,
            p ^ (Nat.card A).factorization p :=
          Finset.prod_finset_coe (fun p ↦ p ^ (Nat.card A).factorization p) _
        _ = (Nat.card A).factorization.prod (· ^ ·) := rfl
        _ = Nat.card A := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne')

end AddCommGroup
end TauCeti
end

public section

open CategoryTheory Matrix

namespace TauCeti

section Table

variable (F : Type) [Field F] [Fintype F] (E : Type*) [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {F E}

theorem exists_equiv_submatrix_GL2CharacterTable_eq {ι κ : Type*} [Finite ι]
    (c : κ → ConjClasses (GL (Fin 2) F)) (hc : Function.Bijective c)
    (M : Matrix ι κ ℂ)
    (hrow : ∀ i : GL2CharacterParam F E, ∃ k, ∀ j, GL2CharacterTable F E i (c j) = M k j)
    (hcard : Nat.card ι ≤ Nat.card (GL2CharacterParam F E)) :
    ∃ e : ι ≃ GL2CharacterParam F E, (GL2CharacterTable F E).submatrix e c = M := by
  -- The common enumeration argument from `CharacterTable.GL2.Field.Three`.
  choose f hf using hrow
  have hinj : Function.Injective f := fun i i' h => by
    refine GL2CharacterParam.coe_classFunction_injective (funext fun g => ?_)
    obtain ⟨j, hj⟩ := hc.surjective (ConjClasses.mk g)
    simp only [← GL2CharacterTable_apply (E := E), ← hj, hf, h]
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hcard
  refine ⟨(Equiv.ofBijective f hbij).symm, Matrix.ext fun k j => ?_⟩
  rw [submatrix_apply, hf, Equiv.ofBijective_apply_symm_apply f hbij k]

end Table
end TauCeti
end

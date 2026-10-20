public section

variable (R L M : Type*)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

variable {R L M} in
lemma LieModule.IsIrreducible.mk [Nontrivial M] (h : ∀ N : LieSubmodule R L M, N ≠ ⊥ → N = ⊤) :
    IsIrreducible R L M :=
  IsSimpleOrder.of_forall_eq_top h

end

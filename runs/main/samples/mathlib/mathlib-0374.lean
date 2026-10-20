@[expose] public section

open scoped Pointwise

theorem mem_galBasis_iff (K L : Type*) [Field K] [Field L] [Algebra K L] (U : Set Gal(L/K)) :
    U ∈ galBasis K L ↔ U ∈ (fun g => g.carrier) '' fixedByFinite K L :=
  Iff.rfl

end

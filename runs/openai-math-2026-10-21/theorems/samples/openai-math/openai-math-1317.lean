namespace OAI

namespace WitnessedSeparation.Counting

noncomputable section

variable {R I A B : Type*} [DecidableEq I]

theorem typeOf_permute (S : Structure R A) (T : Structure R B)
    (names : Finset I) (e : I ≃ I) {v : I → A} {w : I → B}
    (h : typeOf S names v = typeOf T names w) :
    typeOf S (names.map e.symm.toEmbedding) (v ∘ e) =
      typeOf T (names.map e.symm.toEmbedding) (w ∘ e) := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  have hf' : (φ.rename e).free ⊆ names := by
    rw [Formula.free_rename]
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨k,hk,hkj⟩ := Finset.mem_map.mp (hf hj)
    simpa only [Equiv.toEmbedding_apply,← hkj,Equiv.apply_symm_apply] using hk
  simpa using (typeOf_eq_iff _ _ _ _ _).mp h (φ.rename e) hf'

end
end WitnessedSeparation.Counting
end OAI

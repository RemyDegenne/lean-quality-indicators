public section

namespace TauCeti.BinaryGolay

open Finset Matrix

/-- The forty-eight roots, indexed by a coordinate and a sign. The Boolean value `false`
selects `2 eᵢ`, and `true` selects `-2 eᵢ`. -/
noncomputable def rootsEquiv :
    Fin 24 × Bool ≃ constructionALattice.vectorsOfNorm 2 :=
  Equiv.ofBijective
    (fun p ↦ ⟨if p.2 then -coordinateRoot p.1 else coordinateRoot p.1, by
      rw [IntegralLattice.mem_vectorsOfNorm]
      cases p.2
      · exact norm_coordinateRoot p.1
      · simpa only [ite_true, Submodule.coe_neg, IntegralLattice.norm_neg] using
          norm_coordinateRoot p.1⟩) (by
    constructor
    · rintro ⟨i, b⟩ ⟨j, c⟩ h
      have hi := congrArg (fun x : constructionALattice.vectorsOfNorm 2 ↦
        (x.1 : Fin 24 → ℚ) i) h
      have hij : i = j := by
        by_contra hij
        cases b <;> cases c <;>
          norm_num only [Bool.false_eq_true, ite_false, ite_true,
            Submodule.coe_neg, coe_coordinateRoot, Pi.neg_apply, Pi.single_eq_same,
            Pi.single_eq_of_ne hij] at hi
      apply Prod.ext hij
      subst j
      cases b <;> cases c
      · rfl
      · norm_num only [Bool.false_eq_true, ite_false, ite_true,
          Submodule.coe_neg, coe_coordinateRoot, Pi.neg_apply, Pi.single_eq_same] at hi
      · norm_num only [Bool.false_eq_true, ite_false, ite_true,
          Submodule.coe_neg, coe_coordinateRoot, Pi.neg_apply, Pi.single_eq_same] at hi
      · rfl
    · rintro ⟨x, hx⟩
      obtain ⟨i, h | h⟩ := (mem_vectorsOfNorm_two_iff x).mp hx
      · exact ⟨(i, false), Subtype.ext h.symm⟩
      · exact ⟨(i, true), Subtype.ext h.symm⟩)

end TauCeti.BinaryGolay
end

namespace OAI

section

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

open SSet.modelCategoryQuillen

noncomputable section

theorem subcomplex_preimage_isPullback {X E : SSet.{0}} (A : X.Subcomplex) (p : E ⟶ X) :
    IsPullback (A.preimage p).ι (A.fromPreimage p) p A.ι := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    exact Subtype.ext h.1
  · intro x y h
    refine ⟨⟨x, ?_⟩, rfl, ?_⟩
    · change p.app d x ∈ A.obj d
      rw [h]
      exact y.property
    · exact Subtype.ext h

end
end Thomason.Construction
end
end OAI

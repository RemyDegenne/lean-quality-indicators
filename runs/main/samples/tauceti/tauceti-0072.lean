public section

noncomputable section

open QuadraticMap QuadraticForm

namespace TauCeti

variable {K : Type u} {L : Type v} {M : Type w}

variable [Field K] [Field L] [Field M] [Algebra K L]

variable [Invertible (2 : K)] [Invertible (2 : L)]

@[simp]
theorem WittRing.baseChange_wittClass (x : RegularFormClass K) :
    WittRing.baseChange (L := L) (wittClass x) =
      wittClass (RegularFormClass.baseChange L x) := by
  rw [wittClass_apply, wittClass_apply, WittRing.baseChange_mk,
    WittGrothendieckRing.baseChange_toWittGrothendieck]

end TauCeti
end
end

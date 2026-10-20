public section

open Matrix

namespace AffineBasis

variable {ι ι' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

@[simp]
theorem toMatrix_update [DecidableEq ι'] (q : ι' → P) (i : ι') (x : P) :
    b.toMatrix (Function.update q i x) = (b.toMatrix q).updateRow i (b.coords x) := by
  ext j l
  rcases eq_or_ne j i with rfl | hj
  · simp [toMatrix_apply]
  · simp [toMatrix_apply, hj]

end Ring
end AffineBasis
end

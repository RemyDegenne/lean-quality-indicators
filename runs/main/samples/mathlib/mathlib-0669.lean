public section

namespace Projectivization

open Height AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

lemma mulHeight_mk {x : ι → K} (hx : x ≠ 0) : mulHeight (mk K x hx) = Height.mulHeight x := by
  rfl

end Projectivization
end

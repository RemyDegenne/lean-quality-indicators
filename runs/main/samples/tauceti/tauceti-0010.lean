public section

open ContinuousAlternatingMap

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma cotangentLiouvilleForm_eq_coe :
    cotangentLiouvilleForm (V := V) = ⇑(cotangentLiouvilleFormCLM (V := V)) := by
  funext y
  rfl

end TauCeti
end
end

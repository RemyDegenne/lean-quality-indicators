@[expose] public section

namespace GaleStewartGame

open Descriptive Tree Covering Stream'.Discrete

open MeasureTheory CategoryTheory

noncomputable section «Section1»

namespace BorelDet'

variable (T : PTrees) (W : Set (body T.1.2)) {n : ℕ}

lemma closed_unravelable (h : IsClosed W) : UniversallyUnravelable T W := by
  intro T' f; apply BorelDet.main_lemma
  exact h.preimage (LenHom.bodyMap_continuous f.toHom)

end BorelDet'
end «Section1»
end GaleStewartGame
end

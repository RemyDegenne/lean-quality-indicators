namespace OAI

noncomputable section

namespace RationalTerms

local instance rationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E

variable {J A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
 def Term.sub (e f : Term J) : Term J := .add e (.mul (.scalar (-1)) f)

variable (v : J→A) (w : J→B) (h : ∀ e : Term J,‖e.eval w‖≤‖e.eval v‖)

include h

lemma eval_eq_of_norm (e f : Term J) (hef : e.eval v=f.eval v) : e.eval w=f.eval w := by
  have hn := h (e.sub f)
  rw [Term.eval_sub,Term.eval_sub,hef,sub_self,norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
 def liftedValue (x : evalRange v) : B := (Classical.choose x.property).eval w

end RationalTerms
end
end OAI

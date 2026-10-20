public section

namespace HeckeRing.GL2

open HeckeRing.GLn

variable (p : ℕ)

@[simp] lemma upperTriRep_apply_one_zero (b : Fin p) :
    (↑(upperTriRep p b) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 :=
  upperTriGL_apply_eq_zero_of_lt (fun i ↦ by fin_cases i <;> simp [b.pos]) _ (by decide)

end HeckeRing.GL2
end

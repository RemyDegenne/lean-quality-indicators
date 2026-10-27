public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {r : ℕ}

section Form

theorem eq_zero_of_forall_form_eq_zero {u : Fin r ⊕ Fin r → K} (h : ∀ w, form u w = 0) : u = 0 := by
  funext a
  have := h (Pi.single (par a) 1)
  rw [form_single_right, par_par] at this
  simpa [sgn_ne_zero] using this

end Form
end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
end

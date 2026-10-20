public section

namespace MvPolynomial

variable {R σ τ υ : Type*}

theorem lazardValuationReindex_finRotate_symm {n : ℕ} [CommSemiring R]
    (p : MvPolynomial (Fin (n + 1)) R) (a : Fin (n + 1) → R) :
    p.lazardValuationReindex (finRotate (n + 1)).symm a =
      (rename (finRotate (n + 1)).symm p).lazardValuation
        (Fin.snoc (Fin.tail a) (a 0)) := by
  rw [lazardValuationReindex_def, Fin.snoc_eq_cons_rotate]
  rw [Fin.cons_self_tail]
  rfl

end MvPolynomial
end

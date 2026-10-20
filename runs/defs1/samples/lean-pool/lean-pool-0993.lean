@[expose] public section

/-- A matrix in `SL_m(ℤ)` is a transvection if it equals `slTransvecG i j hij c`
for some `i ≠ j` and scalar `c`. -/
def IsTransvec {m : ℕ} (E : Matrix.SpecialLinearGroup (Fin m) ℤ) : Prop :=
  ∃ (i j : Fin m) (hij : i ≠ j) (c : ℤ), E = slTransvecG i j hij c

end

@[expose] public section

noncomputable section

notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

section

@[expose] public section

namespace LeanCert.Core

namespace IntervalDyadic

/-- Fast interval multiplication using sign-based case splitting.
    Reduces from 4 multiplications + 12 comparisons to 2 multiplications
    in the common case (both intervals positive or both negative).
    Falls back to the full 4-way product for mixed-sign intervals. -/
def mulFast (I J : IntervalDyadic) : IntervalDyadic :=
  if hI : Dyadic.le 0 I.lo then
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.lo, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.lo, I.lo.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      ⟨I.hi.mul J.lo, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
  else if hI2 : Dyadic.le I.hi 0 then
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.hi, I.hi.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.hi, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      ⟨I.lo.mul J.hi, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
  else
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.hi, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.lo, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      mul I J

end IntervalDyadic
end LeanCert.Core
end
end
end
end

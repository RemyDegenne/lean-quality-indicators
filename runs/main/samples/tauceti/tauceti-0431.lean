public section

namespace TauCeti.LSeries

open scoped ComplexOrder

variable {a : ℕ → ℂ}

theorem positive_of_exists_pos (ha : 0 ≤ a) (hpos : ∃ n ≠ 0, 0 < a n) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) :
    0 < LSeries a x :=
  positive_of_exists_pos_of_summable ha hpos <|
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa only [Complex.ofReal_re] using hx)

end TauCeti.LSeries
end

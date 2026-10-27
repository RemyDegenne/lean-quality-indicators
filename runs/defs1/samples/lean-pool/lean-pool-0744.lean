@[expose] public section

namespace ZFSet

namespace ZFRat

/-- Rational scalar multiplication through the encoded rational field. -/
noncomputable def qsmul (k : ℚ) (m : ZFRat) : ZFRat := (k : ZFRat) * m

end ZFRat
end ZFSet
end

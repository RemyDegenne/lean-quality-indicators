public section

open Function IsDedekindDomain NumberField

open scoped NNReal NumberField

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

variable {K}

/-- The normalized absolute value at a place of a number field: the `v`-adic absolute value at a
finite place `v`, and `w x ^ w.mult` at an infinite place `w`, so that a real place contributes
`|x|` and a complex place contributes `|x| ^ 2`.

At a complex place this is not subadditive, so it is bundled as a `MonoidWithZeroHom` rather than
as an `AbsoluteValue`. -/
noncomputable def normalizedAbsValue : Place K → K →*₀ ℝ
  | .inl v => (NumberField.HeightOneSpectrum.adicAbv K v).toMonoidWithZeroHom
  | .inr w =>
    { toFun x := w x ^ w.mult
      map_zero' := by simp [zero_pow InfinitePlace.mult_ne_zero]
      map_one' := by simp
      map_mul' x y := by simp [mul_pow] }

end TauCeti.GlobalNumberFields
end

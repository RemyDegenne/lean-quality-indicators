public section

open QuadraticAlgebra

open scoped nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

/-- The second ideal generator `(-b + √D)/2`. -/
def idealGenerator (f : BinaryQuadraticForm ℤ) (D : ℤ) : QuadraticAlgebra ℚ (D : ℚ) 0 :=
  ⟨-(f.b : ℚ) / 2, 1 / 2⟩

end TauCeti.BinaryQuadraticForm
end

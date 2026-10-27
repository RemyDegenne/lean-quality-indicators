@[expose] public section

namespace LeanPool.PythagoreanPolynomialParametrization

open MvPolynomial

/-- A triple of integers (x,y,z) is a Pythagorean triple if x² + y² = z². -/
def IsPythagoreanTriple (x y z : ℤ) : Prop := x^2 + y^2 = z^2

end LeanPool.PythagoreanPolynomialParametrization
end

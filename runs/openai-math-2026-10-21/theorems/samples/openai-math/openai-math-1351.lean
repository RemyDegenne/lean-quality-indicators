namespace OAI

noncomputable section

namespace Ostmann.QuadraticSieve

open Complex

open scoped BigOperators

theorem stdAddChar_four_one : ZMod.stdAddChar (1 : ZMod 4)=I := by
  calc
    _ = Complex.exp (2*(Real.pi : ℂ)*I*1/4) := by
      simpa using (ZMod.stdAddChar_coe (N := 4) 1)
    _ = Complex.exp ((Real.pi : ℂ)/2*I) := by congr 1; ring
    _ = I := Complex.exp_pi_div_two_mul_I

end Ostmann.QuadraticSieve
end
end OAI

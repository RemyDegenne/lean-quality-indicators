public section

namespace TauCeti

open NumberField

open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace IdealArithmeticFunction

theorem vonMangoldtTransform_apply (f : IdealArithmeticFunction K)
    (A : (Ideal (𝓞 K))⁰) :
    f.vonMangoldtTransform A = f A * vonMangoldt A := by
  rw [vonMangoldtTransform, Pi.mul_apply]

end IdealArithmeticFunction
end TauCeti
end

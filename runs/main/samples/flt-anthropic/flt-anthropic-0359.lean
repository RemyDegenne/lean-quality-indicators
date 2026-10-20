namespace P2MW.S_MvPolynomial_CrossingQuotient_one_sub_algebraMap_mul_U_mem_nonZeroDivisors_and_V

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

open scoped Polynomial LaurentPolynomial

namespace NZDKIT

universe u

variable {W : Type u} [CommRing W] (t : W)

theorem φ₂_mk (p : MvPolynomial (Fin 2) W) : φ₂ t (mk t p) = aeval (gen₂ t) p := rfl

end NZDKIT
end P2MW.S_MvPolynomial_CrossingQuotient_one_sub_algebraMap_mul_U_mem_nonZeroDivisors_and_V

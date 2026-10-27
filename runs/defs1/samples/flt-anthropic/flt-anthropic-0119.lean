namespace P2MW.S_RubinSilverberg_not_dvd_den_coeff

namespace RubinSilverberg

p2m_open

open Polynomial IsDedekindDomain

section FieldAlgebra

variable {K : Type*} [Field K]

noncomputable def polyB (b u₀ l : K) : K[X] :=
  C (b / kleinT u₀) * kleinTHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)

end FieldAlgebra
end RubinSilverberg
end P2MW.S_RubinSilverberg_not_dvd_den_coeff

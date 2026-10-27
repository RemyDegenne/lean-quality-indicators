public section

open CFSG.LieType.Ree Equiv

open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem srTi_mod (i : ℕ) : srTi i = srTi (i % 7) := by
  simp only [srTi]
  rw [← orderOf_srG, pow_mod_orderOf]

end CFSG.SignalizerFunctorTheorem.CatalogBridge
end

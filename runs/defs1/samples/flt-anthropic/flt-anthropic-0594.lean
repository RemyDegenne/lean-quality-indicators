namespace P2MW.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne

set_option autoImplicit false

open scoped IntermediateField

open Polynomial

namespace SepLaurent

section Constants

noncomputable def toDerivation {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] [CharP k p] [PerfectRing k p]
    (D : Ω →+ Ω) (hD : ∀ a b : Ω, D (a * b) = a * D b + b * D a) : Derivation k Ω Ω where
  toFun := D
  map_add' := D.map_add
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, Algebra.smul_def, hD, leibniz_map_algebraMap p D hD, mul_zero, add_zero]
  map_one_eq_zero' := leibniz_map_one D hD
  leibniz' a b := by
    change D (a * b) = a * D b + b * D a
    exact hD a b

end Constants
end SepLaurent
end P2MW.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne

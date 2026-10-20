namespace P2MW.S_WeierstrassCurve_exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom

set_option autoImplicit false

namespace P2MKcA

namespace WidthB2

namespace VeluReduction

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

section MapLemmas

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

theorem map_veluGx (x y : R) : (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [veluGx, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
    map_add, map_sub, map_mul, map_pow, map_ofNat]

end MapLemmas
end VeluReduction
end WidthB2
end P2MKcA
end P2MW.S_WeierstrassCurve_exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom

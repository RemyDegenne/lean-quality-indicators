namespace P2MW.S_ModularCurve_comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

p2m_open

namespace ModularCurve

namespace SSPlaceBC

p2m_open

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K] {Γ : Subgroup SL(2, ℤ)}
  (ι : ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ))
  (hι : ∀ x : ↥(qExpFunctionFieldC k Γ),
    ((ι x : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap (algebraMap k K) (x : LaurentSeries k))

theorem eq_jBar_of_coe_eq {L : Type*} [Field L] {Γ : Subgroup SL(2, ℤ)} {x : ↥(qExpFunctionFieldC L Γ)}
    (hx : (x : LaurentSeries L) = jqModC L) : x = jBar L Γ :=
  Subtype.ext hx

end SSPlaceBC
end ModularCurve
end
end P2MW.S_ModularCurve_comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq

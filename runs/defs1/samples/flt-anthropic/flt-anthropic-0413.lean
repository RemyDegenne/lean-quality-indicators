namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ResidualSplitting

section ring

variable {R : Type*} [CommRing R]

p2m_open

noncomputable def quotColonEquivMapSpan (I : Ideal R) (f : R) :
    (R ⧸ I.colon {f}) ≃ₗ[R] ↥(Submodule.map I.mkQ (Ideal.span {f})) :=
  Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_toSpanSingleton I f).symm ≪≫ₗ
    (I.mkQ ∘ₗ LinearMap.toSpanSingleton R R f).quotKerEquivRange ≪≫ₗ
      LinearEquiv.ofEq _ _ (range_mkQ_comp_toSpanSingleton I f)

end ring
end ResidualSplitting
end P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul

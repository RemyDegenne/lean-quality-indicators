namespace P2MW.S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

p2m_open

universe u v w

noncomputable section

namespace P2mSemilin

variable {K : Type u} [Field K]

section Twist

variable {C : Scheme.{u}} {c : C ⟶ (Spec (.of K))} {ε : SchemeHomOver (𝟙 (Spec (.of K))) c}
  {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (e : (Spec (.of K)) ⟶ (Spec (.of K))) [IsIso e] (B : C ≅ C) (hB : B.hom ≫ c ≫ e = c)

include hB in
omit [IsIso e] in
theorem inv_comp_base : B.inv ≫ c = c ≫ e :=
  B.inv_comp_eq.mpr (by simpa only [Category.assoc] using hB.symm)

end Twist
end P2mSemilin
end
end P2MW.S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic

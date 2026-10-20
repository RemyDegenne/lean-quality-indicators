namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section

set_option autoImplicit false

p2m_open

noncomputable section

universe u

namespace MvPolynomial

namespace CrossingQuotient

p2m_open

variable {W : Type u} [CommRing W] (t : W)

namespace Resolution

p2m_open

variable (e : ℕ)

variable {t e}

scoped instance isClosedImmersion_chartSection [IsSeparated (toSpec t e)] (j : Fin e) (a b : W) (h : a * b = t) :
    IsClosedImmersion (chartSection j a b h) := by
  have : IsClosedImmersion (chartSection j a b h ≫ toSpec t e) := by rw [chartSection_toSpec]; infer_instance
  exact .of_comp _ (toSpec t e)

scoped instance isSeparated_toSpec [IsSeparated (toCrossing t e)] : IsSeparated (toSpec t e) := by
  delta toSpec; infer_instance

theorem torusLift_algebraMap (a b : W) (h : a * b = t) (c : CrossingQuotient W t) :
    torusLift a b h (algebraMap (CrossingQuotient W t) (TorusRing t) c) = algebraMap W _ (lift t a b h c) :=
  IsLocalization.Away.lift_eq _ _ c

end Resolution
end CrossingQuotient
end MvPolynomial
end
end P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section

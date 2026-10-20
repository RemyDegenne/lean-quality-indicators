public section

namespace TauCeti

variable (G : Type*) [CommGroup G]

variable {G}

variable {H : Type*} [CommGroup H]

variable {K : Type*} [CommGroup K]

/-- A multiplicative equivalence of commutative groups induces a `ZMod 2`-linear equivalence of
their maximal elementary-2 quotients. -/
noncomputable def elementaryTwoQuotientCongr (e : G ≃* H) :
    ElementaryTwoQuotient G ≃ₗ[ZMod 2] ElementaryTwoQuotient H where
  toLinearMap := elementaryTwoQuotientMap e.toMonoidHom
  invFun := elementaryTwoQuotientMap e.symm.toMonoidHom
  left_inv x := by
    obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
    simp
  right_inv x := by
    obtain ⟨h, rfl⟩ := elementaryTwoQuotientMk_surjective (G := H) x
    simp

end TauCeti
end

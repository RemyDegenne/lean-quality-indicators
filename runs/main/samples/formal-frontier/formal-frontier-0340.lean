public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

theorem jointlySchemeTheoreticallyDominant_iff_iInf_appTop_ker
    (f : ∀ j, X j ⟶ Y) [IsAffine Y] :
    JointlySchemeTheoreticallyDominant f ↔
      (⨅ j, RingHom.ker (f j).appTop.hom) = ⊥ := by
  change (⨅ j, (f j).ker) = ⊥ ↔ _
  rw [← (Scheme.IdealSheafData.equivOfIsAffine (X := Y)).injective.eq_iff]
  simp [Scheme.ker_of_isAffine]

end AlgebraicGeometry
end
end

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced

set_option autoImplicit false

set_option maxHeartbeats 800000

universe u

p2m_open

namespace AlgebraicGeometry

p2m_open

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.le_ofIdeals_iff Hom Γ preimage_basicOpen Hom.imageι basicOpen_zero IdealSheafData.ker_subschemeι basicOpen Hom.ker_apply Opens IdealSheafData.ofIdeals IdealSheafData" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "image app imageι ker preimage_basicOpen ker_apply" end Scheme.Hom

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.ker_le_ker_of_range_subset_closure {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (u : T ⟶ Y) [IsReduced T] (h : Set.range u.base ⊆ closure (Set.range f.base)) :
    f.ker ≤ u.ker := by
  change f.ker ≤ Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (u.app U).hom
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  rw [Scheme.Hom.ker_apply] at hs
  change u.app U s = 0
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen]
  ext1
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h1 : u.base t ∈ (Y.basicOpen s : Set Y) := ht
  have h2 : u.base t ∈ closure (Set.range f.base) := h ⟨t, rfl⟩
  have := Scheme.Hom.basicOpen_inter_closure_range_eq_empty f s hs
  exact (Set.eq_empty_iff_forall_notMem.mp this) (u.base t) ⟨h1, h2⟩

end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced

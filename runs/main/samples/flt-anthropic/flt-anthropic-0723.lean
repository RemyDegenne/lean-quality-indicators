namespace P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom

set_option autoImplicit false

namespace HopfPointsSheafSol

open WithConv

open scoped TensorProduct

p2m_reactivate

section Points

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{0}} (K : Type) [CommRing K] [HopfAlgebra ℤ K]

noncomputable scoped instance instCommGroupPts [PtsComm S K] (U : S.Fppf) :
    CommGroup (Pts K U) :=
  { instGroupWithConv with mul_comm := PtsComm.comm U }

lemma ptOfHom_comp {X Y : Scheme.{0}} (g : Y ⟶ X) (f : X ⟶ Spec (.of K)) :
    ptOfHom K (g ≫ f) = postcomp K (Scheme.Γ.map g.op).hom.toIntAlgHom (ptOfHom K f) := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  unfold ptOfHom
  rw [ringHomOfHom_comp]
  rfl

end Points
end HopfPointsSheafSol
end P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom

namespace P2MW.S_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two

attribute [-instance] EtaleCohomologyLES.instAdditiveSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.instFullSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.constSchemeOpAdditive EtaleCohomologyLES.instFaithfulSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf AlgebraicGeometry.Scheme.instAdditiveSheafFppfSmallFppfTopologyAbFppfCohomologyFunctor EtaleCohomologyLES.idIsContinuousEtaleFppf EtaleCohomologyLES.constantSheafEtaleAdditive EtaleCohomologyLES.constantSheafFppfAdditive EtaleCohomologyLES.etaleTopologySubcanonical EtaleCohomologyLES.etaleSheavesIsGrothendieckAbelian

set_option autoImplicit false

namespace ConvPoints

section Avatar

p2m_open

open scoped Coalgebra

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

open FppfRepresentableGroupSchemeSheaf

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

section Geom

variable (ic : IsCocommW ℤ K)

noncomputable def pointsAb : Scheme.{0}ᵒᵖ ⥤ Ab.{0} where
  obj T :=
    haveI := ic.out
    AddCommGrpCat.of (Additive (WithConv (K →ₐ[ℤ] Γ(T.unop, ⊤))))
  map {T T'} φ :=
    haveI := ic.out
    AddCommGrpCat.ofHom
      (MonoidHom.toAdditive (compConvMonoidHom (C := K) (ringHomToAlgHom φ.unop.appTop.hom)))
  map_id T := by
    haveI := ic.out
    refine AddCommGrpCat.hom_ext ?_
    refine AddMonoidHom.ext fun s => ?_
    refine congrArg Additive.ofMul (ofConv_injective ?_)
    refine AlgHom.ext fun c => ?_
    show (𝟙 T.unop : T.unop ⟶ T.unop).appTop.hom ((Additive.toMul s).ofConv c)
      = (Additive.toMul s).ofConv c
    simp
  map_comp {T T' T''} φ ψ := by
    haveI := ic.out
    refine AddCommGrpCat.hom_ext ?_
    refine AddMonoidHom.ext fun s => ?_
    refine congrArg Additive.ofMul (ofConv_injective ?_)
    refine AlgHom.ext fun c => ?_
    show ((φ ≫ ψ).unop.appTop.hom) ((Additive.toMul s).ofConv c)
      = (ψ.unop.appTop.hom) ((φ.unop.appTop.hom) ((Additive.toMul s).ofConv c))
    simp

end Geom
end Avatar
end ConvPoints
end P2MW.S_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two

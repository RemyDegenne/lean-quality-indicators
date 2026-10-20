namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

namespace X1bSol

namespace SG

open AlgebraicGeometry

variable {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))

theorem isBaseChange_res (F : OModulePresheaf q) (hF : F.IsQuasicoherent) {U : P.Opens} (hU : IsAffineOpen U) (V : P.affineOpens)
    (h : V.1 ≤ U) :
    letI := (ρ P h).toAlgebra
    letI : Module Γ(P, U) (F.obj V.1) := Module.compHom _ (ρ P h)
    ∃ (_ : IsScalarTower Γ(P, U) Γ(P, V.1) (F.obj V.1)) (μ : F.obj U →ₗ[Γ(P, U)] F.obj V.1),
      (∀ x, μ x = F.res h x) ∧ IsBaseChange Γ(P, V.1) μ := by
  letI := (ρ P h).toAlgebra
  letI : Module Γ(P, U) (F.obj V.1) := Module.compHom _ (ρ P h)
  haveI hst : IsScalarTower Γ(P, U) Γ(P, V.1) (F.obj V.1) := IsScalarTower.of_algebraMap_smul fun a x => rfl
  let μ : F.obj U →ₗ[Γ(P, U)] F.obj V.1 :=
    { toFun := F.res h, map_add' := fun x y => map_add _ x y, map_smul' := fun a x => F.res_smul h a x }
  obtain ⟨β, hβ⟩ :=
    AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res F hF ⟨U, hU⟩ V h
  exact ⟨hst, μ, fun x => rfl, IsBaseChange.of_equiv β hβ⟩

end SG
end X1bSol
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective

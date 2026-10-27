public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uM uN uP uQ

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}
  {PP : AInfinityRightModule AA P}

/-- Construct a module morphism from a degree-zero Taylor map satisfying the suspended component
equation. Cofreeness supplies the bar map and reduces its differential law to this equation. -/
noncomputable def ofTaylor (F : (M ⊗[R] TensorWords R A) →ₗ[R] N)
    (hF : LinearMap.IsHomogeneous F (AInfinityRightModule.barGrading AA MM.grading).piece
      (NN.grading.shift 1).piece 0)
    (h : NN.taylor ∘ₗ (Comodule.Hom.cofreeLift (C := TensorWords R A) F).toLinearMap =
      F ∘ₗ MM.barDifferential) : AInfinityRightModuleHom MM NN where
  barHom := Comodule.Hom.cofreeLift F
  isHomogeneous_barMap := isHomogeneous_cofreeLift hF
  barDifferential_comp_barMap := (barDifferential_comp_iff _ (isHomogeneous_cofreeLift hF)).2
    (by
      have hret := (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := N)
        (P := M ⊗[R] TensorWords R A)).apply_symm_apply F
      rw [Comodule.Hom.cofreeEquiv_symm_apply, Comodule.Hom.cofreeEquiv_apply] at hret
      rw [hret]
      exact h)

end AInfinityRightModuleHom
end TauCeti
end

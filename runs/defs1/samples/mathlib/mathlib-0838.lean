@[expose] public section

noncomputable section

open Polynomial IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

variable {F} {K}

variable {K₁ K₂ K₃ : Type*} [Field K₁] [Field K₂] [Field K₃] [Algebra F K₁]
  [Algebra F K₂] [Algebra F K₃] (ϕ : K₁ →ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ →ₐ[F] K₃)
  (ω : K₂ ≃ₐ[F] K₃)

section lift

variable (E : Type*) [Field E] [Algebra F E] [Algebra K₁ E] [Algebra K₂ E] [IsScalarTower F K₁ E]
  [IsScalarTower F K₂ E]

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K₁ →ₐ[F] K₂` to `ϕ.liftNormal E : E →ₐ[F] E`. -/
@[stacks 0BME "Part 2"]
noncomputable def AlgHom.liftNormal [h : Normal F E] : E →ₐ[F] E :=
  @AlgHom.restrictScalars F K₁ E E _ _ _ _ _ _
      ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _ _ _ _ <|
    Nonempty.some <|
      @IntermediateField.nonempty_algHom_of_adjoin_splits _ _ _ _ _ _ _
        ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _
        (fun x _ ↦ ⟨(h.out x).1.tower_top,
          @IsIntegral.minpoly_splits_tower_top F K₁ E E _ _ _ _ _ _ _ _ x
            (RingHom.toAlgebra _) _ _ (h.out x).1 (h.out x).2⟩)
        (IntermediateField.adjoin_univ _ _)

end lift
end
end

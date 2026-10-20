namespace P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion

set_option autoImplicit false

noncomputable section

open scoped TensorProduct IntermediateField Pointwise

namespace AlgebraicCurve

p2m_open

namespace BombieriLower

universe u v

section Construction

variable (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]

scoped instance algKΩ : Algebra (Kc k) (Ω F) := (ιK k F).toRingHom.toAlgebra

scoped instance : IsScalarTower k (Kc k) (Ω F) :=
  IsScalarTower.of_algebraMap_eq fun c => ((ιK k F).commutes c).symm

scoped instance : Field (Fb k F) := inferInstanceAs (Field ↥(FI k F))

scoped instance : Algebra (Kc k) (Fb k F) := inferInstanceAs (Algebra (Kc k) ↥(FI k F))

scoped instance : Algebra (Fb k F) (Ω F) := inferInstanceAs (Algebra ↥(FI k F) (Ω F))

scoped instance : IsScalarTower (Kc k) (Fb k F) (Ω F) :=
  inferInstanceAs (IsScalarTower (Kc k) ↥(FI k F) (Ω F))

scoped instance algebraFFb : Algebra F (Fb k F) :=
  ((algebraMap F (Ω F)).codRestrict (FI k F) fun f => algebraMap_mem_FI k F f).toAlgebra

scoped instance : IsScalarTower F (Fb k F) (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (x : F)

scoped instance : Field (Lb k F x) := inferInstanceAs (Field ↥(LI k F x))

scoped instance : Algebra (Kc k) (Lb k F x) := inferInstanceAs (Algebra (Kc k) ↥(LI k F x))

scoped instance : Algebra (Lb k F x) (Ω F) := inferInstanceAs (Algebra ↥(LI k F x) (Ω F))

scoped instance : IsScalarTower (Kc k) (Lb k F x) (Ω F) :=
  inferInstanceAs (IsScalarTower (Kc k) ↥(LI k F x) (Ω F))

scoped instance algLF : Algebra (Lb k F x) (Fb k F) :=
  (IntermediateField.inclusion (LI_le_FI k F x) : ↥(LI k F x) →ₐ[Kc k] ↥(FI k F)).toAlgebra

scoped instance : IsScalarTower (Kc k) (Lb k F x) (Fb k F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (Lb k F x) (Fb k F) (Ω F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : Field (Eb k F x) := inferInstanceAs (Field ↥(EI k F x))

scoped instance : Algebra (Kc k) (Eb k F x) := inferInstanceAs (Algebra (Kc k) ↥(EI k F x))

scoped instance : Algebra (Eb k F x) (Ω F) := inferInstanceAs (Algebra ↥(EI k F x) (Ω F))

scoped instance : IsScalarTower (Kc k) (Eb k F x) (Ω F) :=
  inferInstanceAs (IsScalarTower (Kc k) ↥(EI k F x) (Ω F))

scoped instance algLE : Algebra (Lb k F x) (Eb k F x) :=
  (IntermediateField.inclusion (LI_le_EI k F x) : ↥(LI k F x) →ₐ[Kc k] ↥(EI k F x)).toAlgebra

scoped instance algFE : Algebra (Fb k F) (Eb k F x) :=
  (IntermediateField.inclusion (FI_le_EI k F x) : ↥(FI k F) →ₐ[Kc k] ↥(EI k F x)).toAlgebra

scoped instance : IsScalarTower (Kc k) (Lb k F x) (Eb k F x) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (Kc k) (Fb k F) (Eb k F x) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (Lb k F x) (Fb k F) (Eb k F x) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (Lb k F x) (Eb k F x) (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (Fb k F) (Eb k F x) (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance algkxL : Algebra (kx k F x) (Lb k F x) :=
  ((algebraMap (kx k F x) (Ω F)).codRestrict (LI k F x) (algebraMap_kx_mem_LI k F x)).toAlgebra

scoped instance : IsScalarTower (kx k F x) (Lb k F x) (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (kx k F x) F (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance finite_LF [FiniteDimensional (kx k F x) F] : Module.Finite (Lb k F x) (Fb k F) := by
  obtain ⟨n, b, hb⟩ := exists_span_FI k F x
  let N := Submodule.span (Lb k F x) (Set.range b)
  haveI : Module.Finite (Lb k F x) N := Module.Finite.span_of_finite _ (Set.finite_range b)
  let f : Fb k F →ₗ[Lb k F x] N :=
    LinearMap.codRestrict N (IsScalarTower.toAlgHom (Lb k F x) (Fb k F) (Ω F)).toLinearMap
      fun y => hb y.2
  exact Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg Subtype.val h :)

scoped instance isSeparable_LF [Algebra.IsSeparable (kx k F x) F] : Algebra.IsSeparable (Lb k F x) (Fb k F) := by
  refine ⟨fun y => ?_⟩
  have hy : IsSeparable (Lb k F x) y.1 :=
    (mem_separableClosure_iff.mp (FI_le_separableClosure k F x y.2))
  unfold IsSeparable at hy ⊢
  rwa [← minpoly.algHom_eq (IsScalarTower.toAlgHom (Lb k F x) (Fb k F) (Ω F))
    (RingHom.injective _) y]

scoped instance isAlgebraic_FΩ : Algebra.IsAlgebraic (Fb k F) (Ω F) :=
  ⟨fun z => IsAlgebraic.tower_top (Fb k F) (Algebra.IsAlgebraic.isAlgebraic (R := F) z)⟩

scoped instance isAlgebraic_LΩ [FiniteDimensional (kx k F x) F] : Algebra.IsAlgebraic (Lb k F x) (Ω F) :=
  Algebra.IsAlgebraic.trans (Lb k F x) (Fb k F) (Ω F)

scoped instance isAlgClosure_LΩ [FiniteDimensional (kx k F x) F] : IsAlgClosure (Lb k F x) (Ω F) :=
  ⟨inferInstance, inferInstance⟩

scoped instance finite_LEIL [FiniteDimensional (kx k F x) F] : FiniteDimensional (Lb k F x) ↥(EIL k F x) := by
  unfold EIL; infer_instance

scoped instance isSeparable_LEIL [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    Algebra.IsSeparable (Lb k F x) ↥(EIL k F x) := by
  unfold EIL
  rw [IntermediateField.normalClosure]
  haveI : ∀ f : Fb k F →ₐ[Lb k F x] Ω F, Algebra.IsSeparable (Lb k F x) f.fieldRange := fun f =>
    Algebra.IsSeparable.of_algHom (Lb k F x) (Fb k F)
      (((AlgEquiv.ofInjectiveField f).symm : f.range →ₐ[Lb k F x] Fb k F).comp (fieldRangeToRange f))
  exact IntermediateField.isSeparable_iSup (Lb k F x) (Ω F)

scoped instance isGalois_LEIL [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    IsGalois (Lb k F x) ↥(EIL k F x) := by
  haveI : Normal (Lb k F x) ↥(EIL k F x) := by unfold EIL; infer_instance
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

scoped instance finite_LE [FiniteDimensional (kx k F x) F] : FiniteDimensional (Lb k F x) (Eb k F x) :=
  LinearEquiv.finiteDimensional (ebEquiv k F x).toLinearEquiv

scoped instance isGalois_LE [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    IsGalois (Lb k F x) (Eb k F x) := IsGalois.of_algEquiv (ebEquiv k F x)

scoped instance finite_FE [FiniteDimensional (kx k F x) F] : FiniteDimensional (Fb k F) (Eb k F x) :=
  Module.Finite.of_restrictScalars_finite (Lb k F x) (Fb k F) (Eb k F x)

scoped instance isGalois_FE [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    IsGalois (Fb k F) (Eb k F x) :=
  IsGalois.tower_top_of_isGalois (Lb k F x) (Fb k F) (Eb k F x)

variable {k F x}

variable (k F x)

variable {k F x}

variable (k F x)

section Frobenius

variable {k F x}

variable (p n : ℕ) [Fact p.Prime] [CharP k p]

scoped instance charP_K : CharP (Kc k) p := charP_of_injective_algebraMap (algebraMap k (Kc k)).injective p

scoped instance expChar_K : ExpChar (Kc k) p := ExpChar.prime Fact.out

variable [Finite k]

omit [Fact p.Prime] [CharP k p] in
theorem pow_q_eq_of_mem_k (hq : Nat.card k = p ^ n) (c : k) : c ^ p ^ n = c := by
  haveI := Fintype.ofFinite k
  rw [← hq, Nat.card_eq_fintype_card, FiniteField.pow_card]

end Frobenius
end Construction
end BombieriLower
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places

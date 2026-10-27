namespace P2MW.S_NumberField_distribHaarChar_idelicNorm_genuineBaseChange

set_option autoImplicit false

open scoped TensorProduct NNReal

namespace R2FafNAMod

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge M4aHerbrand.GenuineDescent MeasureTheory

section Genuine

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "𝔸K" => AdeleRing (𝓞 K) K

local notation "𝔸L" => AdeleRing (𝓞 L) L

attribute [local instance] instAlg

attribute [local instance] instMeas

attribute [local instance] instBorel

variable [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in

noncomputable def actCAE (τ : L ≃ₐ[K] L) : (𝔸L) ≃A[ℤ] (𝔸L) :=
  { AlgEquiv.ofRingEquiv (f := ((genuineDescentDatum K L).act τ : (𝔸L) ≃+* (𝔸L)))
      (fun n => by simp) with
    continuous_toFun := (genuineDescentDatum K L).continuous_act τ
    continuous_invFun := by
      have h : ((genuineDescentDatum K L).act τ).symm = (genuineDescentDatum K L).act τ⁻¹ := by
        rw [map_inv]; rfl
      show Continuous (fun x => ((genuineDescentDatum K L).act τ).symm x)
      rw [h]
      exact (genuineDescentDatum K L).continuous_act τ⁻¹ }

end Genuine
end R2FafNAMod
end P2MW.S_NumberField_distribHaarChar_idelicNorm_genuineBaseChange

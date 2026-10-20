namespace P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities

attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

noncomputable section

open CohCarrier IsLocalRing

namespace TWAlpha

section Companions

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V W : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup W] [Module 𝒪 W]
  (DV : HeckeData 𝒪 V k) (DW : HeckeData 𝒪 W k)
  {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σW : G ⊕ Unit ≃ DW.Gen)
  (ι : V →ₗ[𝒪] W) (j : W →ₗ[𝒪] V) (w : Module.End 𝒪 W) (q : ℕ) (d : G)
  (hdV : IsUnit (DV.op (σV (Sum.inl d))))

local notation "T♭" => DV.op (σV (Sum.inr ()))

local notation "U♭" => DW.op (σW (Sum.inr ()))

local notation "Dv" => DV.op (σV (Sum.inl d))

local notation "Dw" => DW.op (σW (Sum.inl d))

local notation "Dvi" => DvInv DV σV d

local notation "XV" => fun g : G => DV.op (σV (Sum.inl g))

local notation "YW" => fun g : G => DW.op (σW (Sum.inl g))

local notation "P♯" => Car DW.FreeAlg (V × V) (modP DV DW σV σW q d hdV)

local notation "P'♯" => Car DW.FreeAlg (V × V) (modP' DV DW σV σW q d hdV)

scoped instance instTowerP : IsScalarTower 𝒪 DW.FreeAlg P♯ := (DU DV DW σV σW q d hdV).V_isScalarTower

scoped instance instTowerP' : IsScalarTower 𝒪 DW.FreeAlg P'♯ := (DU' DV DW σV σW q d hdV).V_isScalarTower

section Maps

variable (hι : ∀ g : G, ι ∘ₗ DV.op (σV (Sum.inl g)) = DW.op (σW (Sum.inl g)) ∘ₗ ι)
  (hj : ∀ g : G, j ∘ₗ DW.op (σW (Sum.inl g)) = DV.op (σV (Sum.inl g)) ∘ₗ j)
  (hw : ∀ g : G, w * DW.op (σW (Sum.inl g)) = DW.op (σW (Sum.inl g)) * w)
  (hdW : IsUnit (DW.op (σW (Sum.inl d))))
  (h₁ : w ∘ₗ ι = (ι ∘ₗ DV.op (σV (Sum.inr ())) - DW.op (σW (Sum.inr ())) ∘ₗ ι) ∘ₗ
    DV.op (σV (Sum.inl d)))
  (h₂ : j ∘ₗ ι = ((q : 𝒪) + 1) • LinearMap.id)
  (h₃ : j ∘ₗ w ∘ₗ ι = DV.op (σV (Sum.inr ())) * DV.op (σV (Sum.inl d)))
  (h₄ : ι ∘ₗ j = LinearMap.id + DW.op (σW (Sum.inr ())) * w)
  (h₅ : w * w = DW.op (σW (Sum.inl d)))

include hdV hj h₂ h₃ h₅ in

theorem adjO_jO_ιO (p : V × V) : adjO DV σV q d (jO j w (ιO ι w p)) = diag (detV DV σV q d) p := by
  rw [jO_ιO (hj := hj) (h₂ := h₂) (h₃ := h₃) (h₅ := h₅), adjO_apply, diag_apply, detV_apply, detV_apply]
  obtain ⟨v₁, v₂⟩ := p
  simp only [map_add, LinearMap.map_smul_of_tower, T_Dv DV σV d, Prod.mk.injEq]
  constructor <;> module

end Maps
end Companions
end TWAlpha
end
end P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities

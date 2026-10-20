namespace P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

attribute [-instance] Quotient.instLE_mathlib

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_NormCosetIndex

set_option autoImplicit false

open NumberField

namespace M4aHerbrand

namespace NormCoset

p2m_open

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

p2m_reactivate

open Descent

section Main

variable [IsGalois K L]

variable (D : IdeleGaloisDescent (𝓞 L) K L) (β : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L)

scoped instance instNormalTate (σ : L ≃ₐ[K] L) :
    ((ideleClassNorm D).range.subgroupOf (ideleClassDerive D σ).ker).Normal :=
  ⟨fun a ha b => by rwa [mul_comm b a, mul_assoc, mul_inv_cancel, mul_one]⟩

theorem toTate_apply
    (hfix : ∀ u : (AdeleRing (𝓞 L) L)ˣ, (∀ τ : L ≃ₐ[K] L, D.unitsAct τ u = u) ↔ u ∈ (Units.map β.toMonoidHom).range)
    (σ : L ≃ₐ[K] L) (v : (AdeleRing (𝓞 K) K)ˣ) :
    toTate D β hfix σ v = QuotientGroup.mk ⟨classOfβ β v, classOfβ_mem_ker D β hfix σ v⟩ := rfl

end Main
end
end NormCoset
end M4aHerbrand
end Fold_NormCosetIndex
end P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd

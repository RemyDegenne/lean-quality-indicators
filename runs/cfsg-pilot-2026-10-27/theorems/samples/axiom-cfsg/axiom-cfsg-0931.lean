public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup)

open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚

theorem map_conj_t_Y1 (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)}
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁)) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (prodFactorOne ψ₂) =
      prodFactorTwo ψ₂ :=
  map_conj_prodFactorOne_of_swap ψ₂ (hS.sec3_12_two.2.1 hS.t_mem_H2) hS.t_mul_t hψt₂

end Setting
end CFSG.LocalAnalysis.EvenBN.U4
end

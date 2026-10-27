public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisSecondAxis

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD

open scoped Matrix commutatorElement Pointwise

section Main

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

local notation "𝐰" => ((φ.symm (sElt swapSL) : L) : G)

local notation "𝐏" => pull φ (antiUnipotent K)

local notation "𝐙" => pull φ (antiUnipotentCenter K)

local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ TG : Subgroup G)

local notation "𝐔₁" => pull φ (rootU K Axis.one)

local notation "𝐔₂" => pull φ (rootU K Axis.two)

local notation "𝐀₁" => pull φ (rootA K Axis.one)

local notation "𝐀₂" => pull φ (rootA K Axis.two)

local notation "𝐁₁" => (zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G)

local notation "𝐁₂" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)

local notation "𝐍₁" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G)

local notation "𝐍₂" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)

set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

set_option quotPrecheck false in
local notation "𝐃₁" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G)).subtype

set_option quotPrecheck false in
local notation "𝐃₂" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype

set_option quotPrecheck false in
local notation "𝐑" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.one) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.one) : Subgroup G) : Set G)).subtype : Subgroup G)

set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype : Subgroup G)

set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)

set_option quotPrecheck false in
local notation "𝐌w" => M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom

set_option quotPrecheck false in
local notation "𝐌₂" =>
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom : Subgroup G)

set_option quotPrecheck false in
local notation "𝐌₀" => (M ⊔ pull φ (rootA K Axis.two) : Subgroup G)

set_option quotPrecheck false in
local notation "𝐄" => (M ⊔ pull φ (antiUnipotent K) : Subgroup G)

set_option quotPrecheck false in
local notation "𝐕" => (M ⊔ pull φ (rootA K Axis.one) ⊔
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom) : Subgroup G)

theorem D₂_le_normalizer [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {H : Subgroup G}
    (hA : 𝐀₂ ≤ H) (hHD : H ≤ 𝐃₂) : 𝐃₂ ≤ normalizer (H : Set G) := fun d hd =>
  mem_normalizer_of_conj_le fun h hH => by
    have hc : d * h * d⁻¹ * h⁻¹ ∈ 𝐀₂ := by
      rw [← (part_three hh).1, ← commutatorElement_def]
      exact commutator_mem_commutator hd (hHD hH)
    have e : d * h * d⁻¹ = (d * h * d⁻¹ * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (hA hc) hH

end Main
end OneAxisSecondAxis
end CFSG.LocalAnalysis.SymplecticFourStandard
end

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace NextCores

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD

open scoped Matrix Pointwise

section FirstCore

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)

local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)

local notation "𝐙" => pull φ (antiUnipotentCenter K)

local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)

local notation "𝐕[" i "]" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)

local notation "𝐀[" i "]" => pull φ (rootA K i)

local notation "𝐔[" i "]" => pull φ (rootU K i)

local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)

local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)

set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype

set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype

set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

local notation "𝐉" => pull φ (diagTorus K)

set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}

local notation "𝐉[" i "]" => pull φ (axisTorus K i)

set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)

set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)

set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐍ₕ[" i "]" => (normalizer ((𝐇 : Subgroup G) : Set G) ⊓
  normalizer (𝐔[i] : Set G) : Subgroup G)

set_option quotPrecheck false in
local notation "𝐃𝐧[" i "]" => normalizer ((𝐃[i] : Subgroup G) : Set G)

set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype

theorem actHyp₁ (h : FCHyp L K n φ t) (i : Axis) :
    FullCenter.ActHyp (psiK φ t i) t 𝐊[i] 𝐀[i] 𝐃𝐧[i] where
  U_le := le_sup_left
  add := fun _ hx _ hy => psiK_mul h i hx hy
  ker := fun _ hx => psiK_eq_zero_iff h i hx
  surj := exists_psiK_eq h i
  conj_A := fun _ hg _ hx => conj_mem_K_of_normalizer_D h i hg hx
  conj_U := fun _ hg _ ha => conj_mem_A_of_normalizer_D h i hg ha
  conj_t := fun _ hg => conj_t_mem_K h i hg

end FirstCore
end NextCores
end CFSG.LocalAnalysis.SymplecticFourStandard
end

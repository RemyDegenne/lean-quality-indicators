public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixF

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores RootStandard

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

open scoped Matrix Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)

local notation "𝐙" => pull φ (antiUnipotentCenter K)

local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)

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
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)

local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)

set_option quotPrecheck false in
local notation "𝐅ʷ[" i "]" => (𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)

set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅ʷ[i] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐃𝐧[" i "]" => normalizer ((𝐃[i] : Subgroup G) : Set G)

set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype

set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)

set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype

set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}

set_option quotPrecheck false in
local notation "𝐕[" i "," k "]" => (𝐌₀[i] ⊓ centralizer (𝐉[k] : Set G) : Subgroup G)

set_option quotPrecheck false in
local notation "𝐌ʷ[" i "," k "]" => (𝐌₀[i].map (MulAut.conj 𝐰[k]⁻¹).toMonoidHom : Subgroup G)

theorem Mhat_sup_t (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : (𝐌₀[i] ⊔ 𝐌ʷ[i, i]) ⊔ zpowers t = 𝐏₁[i] := by
  refine le_antisymm (sup_le (Mhat_le_P₁ h i hne hbot)
    (zpowers_le.mpr (E_le_P₁ h i hne hbot (t_mem_E h i)))) fun p hp => ?_
  rw [← SetLike.mem_coe, ← Mhat_mul_E h i hne hbot] at hp
  obtain ⟨m, hm, e, he, rfl⟩ := hp
  refine mul_mem (mem_sup_left hm) ?_
  rcases mem_X_or_of_mem_E h i he with hx | hx
  · exact mem_sup_left ((Mhat_inf_E h i hne hbot).ge hx).1
  · rw [show e = t⁻¹ * (t * e) by group]
    exact mul_mem (mem_sup_right (inv_mem (mem_zpowers t)))
      (mem_sup_left ((Mhat_inf_E h i hne hbot).ge hx).1)

end SixF
end CFSG.LocalAnalysis.SymplecticFourStandard
end

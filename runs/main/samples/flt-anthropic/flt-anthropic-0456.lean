namespace P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace CerednikDrinfeld

namespace FormalOmega

namespace T3Aux

p2m_open

open TensorProduct CerednikDrinfeld.FormalOmega.LevelAux

p2m_reactivate

section KeyU

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem mem_line_of_coordEquiv_mem (x : AdicPoint K π R) (n : ℕ)
    (y : latticeBaseChange 𝒪 K (modPow π R n) (stdFullLattice K))
    (h : coordEquiv (𝒪 := 𝒪) K (modPow π R n) y ∈ lineCoord x n) : y ∈ (x.pt n).line (stdFullLattice K) := by
  rw [lineCoord, Submodule.mem_map] at h
  obtain ⟨y', hy', hyv⟩ := h
  rw [LinearEquiv.coe_coe] at hyv
  rwa [(coordEquiv (𝒪 := 𝒪) K (modPow π R n)).injective hyv] at hy'

end KeyU
end T3Aux
end FormalOmega
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow

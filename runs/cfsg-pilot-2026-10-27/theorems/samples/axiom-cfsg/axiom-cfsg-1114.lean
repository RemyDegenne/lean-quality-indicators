public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix CFSG.Open Subgroup

open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LieType.Universal.Unitary (SU)

open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)

open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor diagU diagU_val permGL_conj_diagU
  permGL_mem_SU)

open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD weyl₂ shortSL coe_iotaS blkS
  coe_torusD perfectResidual_short perfectResidual_conj conj_weyl₂
  nonempty_shortSL_mulEquiv_galois
  entry_eq_zero_of_commute commute_of_mem_centralizer)

open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

theorem u4_exists_centP (hb : 0 < b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ b + 1)
    {ℓ : Subgroup (GL (Fin 4) F)}
    (hℓ : ℓ = zpowers (torusD ((ω, ω) : D8Mod 3 F)) ∨
      ℓ = zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) :
    ∃ D₀ : Subgroup (GL (Fin 4) F), D₀ ≤ F08.KOf8103 (SU (unitaryInvolution F 2 b) 4) ℓ ∧
      Nat.card D₀ = p ∧
      D₀ ≤ centralizer ((SU (unitaryInvolution F 2 b) 4 ⊓
        centralizer (d8Tor 3 F 4 : Set (GL (Fin 4) F)) : Subgroup (GL (Fin 4) F)) :
          Set (GL (Fin 4) F)) := by
  have hσσ : ∀ c, unitaryInvolution F 2 b (unitaryInvolution F 2 b c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨d, hdord, hd_shortSL, hd_shortSL4, hd_cent⟩ :=
    exists_diagU_four_centP hF hω hp hpq
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois (unitaryInvolution F 2 b) hb hF
  have hperfS : ⁅shortSL (unitaryInvolution F 2 b),
      shortSL (unitaryInvolution F 2 b)⁆ = shortSL (unitaryInvolution F 2 b) :=
    Subgroup.isPerfect_iff.mp
      (CFSG.RankThree.PartTwo.Sec21.isPerfect_of_mulEquiv_projSL (by omega) eS)
  obtain ⟨a, hainv, ht3⟩ := torusD_three_diag hω
  have hS3 : inSubgroup perfectResidual
      (SU (unitaryInvolution F 2 b) 4 ⊓ Subgroup.centralizer
        (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      shortSL (unitaryInvolution F 2 b) :=
    perfectResidual_short (unitaryInvolution F 2 b) hσσ ht3 hainv hperfS
  have hw2 : weyl₂ ∈ SU (unitaryInvolution F 2 b) 4 :=
    permGL_mem_SU (unitaryInvolution F 2 b) _ (by decide)
  have hL4 : Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) =
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
        (MulAut.conj weyl₂).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₂ ((ω, ω) : D8Mod 3 F)).symm
  have hS4 : inSubgroup perfectResidual
      (SU (unitaryInvolution F 2 b) 4 ⊓ Subgroup.centralizer
        (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      (shortSL (unitaryInvolution F 2 b)).map (MulAut.conj weyl₂).toMonoidHom := by
    rw [hL4, perfectResidual_conj hw2, hS3]
  have hK3 : F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) =
      shortSL (unitaryInvolution F 2 b) := hS3
  have hK4 : F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
      (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL (unitaryInvolution F 2 b)).map (MulAut.conj weyl₂).toMonoidHom := hS4
  refine ⟨Subgroup.zpowers d, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    rcases hℓ with hℓ | hℓ
    · rw [hℓ, hK3]
      exact hd_shortSL
    · rw [hℓ, hK4]
      exact hd_shortSL4
  · rw [Nat.card_zpowers, hdord]
  · rw [Subgroup.zpowers_le]
    exact hd_cent

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
end

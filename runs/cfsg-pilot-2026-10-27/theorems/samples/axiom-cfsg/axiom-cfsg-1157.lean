public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace CLSFourGroupScalarSquare

open Matrix FourGroupOddBilinear FourGroupOddUnitary QuaternionMatrices UnitaryHigher Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem odd_symplectic_scalar_square_centralizer_projective_four_group [Finite K]
    (hK : ringChar K ≠ 2) [FiniteDimensional K V] {r : ℕ} (hr : 2 ≤ r)
    (hdim : finrank K V = 2 * r) {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {A : LinearMap.GeneralLinearGroup K V}
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1) {d : K} (hd0 : d ≠ 0)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) :
    ∃ W : Subgroup (SymplecticProj B),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK' : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hε, hsqcase, hnscase⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hK
    n.pos hK' (by omega : 1 ≤ r) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, h1, h2'⟩ := hsqcase l hl
    rcases hε with hε | hε
    · obtain ⟨-, hAp, hAm, hNp, hNm, e, he⟩ := h1 hε
      exact exists_four_split hK hP hM hAp hAm hNp hNm e he
    · obtain ⟨-, -, hrp, -, -, -, e, he, -⟩ := h2' hε
      exact exists_four_paired h2 hr hrp e he
  · push Not at hsq
    obtain ⟨-, -, hcardE, hrankE, bar, -, hbar, -, hc1, hc2⟩ := hnscase hsq
    rcases hε with hε | hε
    · obtain ⟨BE, -, hBEa, hBEn, -, hiff⟩ := hc1 hε
      exact exists_four_field_alt hAA hsq hK BE hBEa hBEn hiff
    · obtain ⟨hf, -, hsymm, hsep, hiff⟩ := hc2 hε
      exact exists_four_field_herm hAA hsq hK hℓ n.pos hcardE (by rw [hrankE]; exact hr) bar
        hbar hf hsymm hsep hiff

end CLSFourGroupScalarSquare
end CFSG.LocalAnalysis.ComponentInitial
end

@[expose] public section

namespace Bananas

open Utilities

open scoped BigOperators

theorem paperReducedPositionCoordinates_eq_of_divisor_eq
    {g : ℕ} (B : Banana g)
    (p q : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hp : IsPaperReducedPositionCoordinates B p)
    (hq : IsPaperReducedPositionCoordinates B q)
    (hDiv : bananaPositionCoordinateDivisor B p =
      bananaPositionCoordinateDivisor B q) :
    p = q := by
  classical
  let P := paperTerminalSlots B p
  let Q := paperTerminalSlots B q
  have hInteriorP : ∀ alpha, IsPaperInteriorCoordinate B p alpha →
      p alpha = q alpha :=
    positionCoordinate_eq_of_interior_of_divisor_eq B p q hDiv
  have hInteriorQ : ∀ alpha, IsPaperInteriorCoordinate B q alpha →
      q alpha = p alpha :=
    positionCoordinate_eq_of_interior_of_divisor_eq B q p hDiv.symm
  have hCard : P.card = Q.card := by
    simpa [P, Q] using paperTerminalSlots_card_eq_of_divisor_eq B p q hDiv
  have hSubset : P ⊆ Q := by
    intro alpha hAlphaP
    by_contra hAlphaQ
    have hpFull : (p alpha).val = B.length alpha := by
      simpa [P, paperTerminalSlots] using hAlphaP
    have hqNotFull : (q alpha).val ≠ B.length alpha := by
      simpa [Q, paperTerminalSlots] using hAlphaQ
    have hqNotInterior : ¬ IsPaperInteriorCoordinate B q alpha := by
      intro hInt
      have heq := hInteriorQ alpha hInt
      have hpBound := (p alpha).isLt
      change 0 < (q alpha).val ∧ (q alpha).val < B.length alpha at hInt
      rw [heq] at hInt
      omega
    have hqZero : (q alpha).val = 0 := by
      have hqBound := (q alpha).isLt
      change ¬ (0 < (q alpha).val ∧
        (q alpha).val < B.length alpha) at hqNotInterior
      omega
    have hExists : ∃ beta, beta ∈ Q ∧ beta ∉ P := by
      by_contra hNo
      push Not at hNo
      have hSubset : Q ⊆ P := fun beta hBeta => hNo beta hBeta
      have hEq : Q = P := Finset.eq_of_subset_of_card_le hSubset (by omega)
      exact hAlphaQ (hEq.symm ▸ hAlphaP)
    obtain ⟨beta, hBetaQ, hBetaP⟩ := hExists
    have hqFull : (q beta).val = B.length beta := by
      simpa [Q, paperTerminalSlots] using hBetaQ
    have hpNotFull : (p beta).val ≠ B.length beta := by
      simpa [P, paperTerminalSlots] using hBetaP
    have hpNotInterior : ¬ IsPaperInteriorCoordinate B p beta := by
      intro hInt
      have heq := hInteriorP beta hInt
      change 0 < (p beta).val ∧ (p beta).val < B.length beta at hInt
      rw [heq] at hInt
      omega
    have hpZero : (p beta).val = 0 := by
      have hpBound := (p beta).isLt
      change ¬ (0 < (p beta).val ∧
        (p beta).val < B.length beta) at hpNotInterior
      omega
    have hab := hp.2 alpha beta hpFull hpZero
    have hba := hq.2 beta alpha hqFull hqZero
    omega
  have hTerminal : P = Q :=
    Finset.eq_of_subset_of_card_le hSubset (by omega)
  funext alpha
  by_cases hpInt : IsPaperInteriorCoordinate B p alpha
  · exact hInteriorP alpha hpInt
  have hqInt : ¬ IsPaperInteriorCoordinate B q alpha := by
    intro hInt
    have heq := hInteriorQ alpha hInt
    change 0 < (q alpha).val ∧ (q alpha).val < B.length alpha at hInt
    rw [heq] at hInt
    change ¬ (0 < (p alpha).val ∧
      (p alpha).val < B.length alpha) at hpInt
    exact hpInt hInt
  by_cases hpFull : (p alpha).val = B.length alpha
  · have hpMem : alpha ∈ P := by simp [P, paperTerminalSlots, hpFull]
    have hqMem : alpha ∈ Q := hTerminal ▸ hpMem
    have hqFull : (q alpha).val = B.length alpha := by
      simpa [Q, paperTerminalSlots] using hqMem
    exact Fin.ext (hpFull.trans hqFull.symm)
  · have hpZero : (p alpha).val = 0 := by
      have hpBound := (p alpha).isLt
      change ¬ (0 < (p alpha).val ∧
        (p alpha).val < B.length alpha) at hpInt
      omega
    have hpNotMem : alpha ∉ P := by simp [P, paperTerminalSlots, hpFull]
    have hqNotMem : alpha ∉ Q := by simpa [hTerminal] using hpNotMem
    have hqNotFull : (q alpha).val ≠ B.length alpha := by
      simpa [Q, paperTerminalSlots] using hqNotMem
    have hqZero : (q alpha).val = 0 := by
      have hqBound := (q alpha).isLt
      change ¬ (0 < (q alpha).val ∧
        (q alpha).val < B.length alpha) at hqInt
      omega
    exact Fin.ext (hpZero.trans hqZero.symm)

end Bananas
end

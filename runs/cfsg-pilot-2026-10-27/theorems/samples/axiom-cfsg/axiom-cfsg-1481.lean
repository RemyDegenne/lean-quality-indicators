public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

set_option linter.unusedSectionVars false

section CaseJK

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {x : Q}

theorem cjk_le_centralizer {T : Subgroup Q}
    (hTB : B ≤ Subgroup.normalizer (T : Set Q))
    (htriv : ∀ t ∈ T, ∀ l ∈ L, t * l = l * t) :
    T ≤ Subgroup.centralizer (t113K B L : Set Q) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hle : t113K B L ≤ Subgroup.centralizer ({t} : Set Q) := by
    refine iSup₂_le fun g hg w hw => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ht' : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hTB hg) t).1 ht
    have h := htriv _ ht' _ (mem_gLBConj.1 hw)
    calc w * t = g⁻¹ * ((g * w * g⁻¹) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (g * w * g⁻¹)) * g := by rw [← h]
      _ = t * w := by group
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)

end CaseJK
end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
end

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg Module

section Abelian

theorem exists_mid_aux : ∀ g ∈ e6R, ∀ d ∈ e6R, List.zipWith (· + ·) g d ∈ Tag.E6.artifactRoots →
    ∃ m ∈ Tag.E6.artifactRoots, List.zipWith (· + ·) d m ∉ Tag.E6.artifactRoots ∧
      List.zipWith (· + ·) d m ≠ List.replicate 6 0 ∧
      List.zipWith (· + ·) g m ∈ Tag.E6.artifactRoots ∧
      List.zipWith (· + ·) d (List.zipWith (· + ·) g m) ∈ Tag.E6.artifactRoots := by
  decide +kernel

end Abelian
end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
end

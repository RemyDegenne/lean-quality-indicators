namespace OAI

namespace PiExponent.GlobalSectionClearing

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable {X Y : Scheme.{u}}

theorem global_section_zero [CompactSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M ⊤)
    (hx : openRestriction M (X.basicOpen_le r) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  apply compact_open_section_zero M r ⊤ isCompact_univ x
  exact openRestriction_zero_congr M (top_inf_eq (a := X.basicOpen r)).symm _ _ _ hx

end
end PiExponent.GlobalSectionClearing
end OAI

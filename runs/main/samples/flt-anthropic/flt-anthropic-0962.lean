namespace P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed

open WeierstrassCurve

namespace P2MKcCQJbc

variable {A B : Type*} [Field A] [Field B] [DecidableEq A] [DecidableEq B] (f : A →+* B)

theorem sigma_eq_of_eq {V₁ V₂ : WeierstrassCurve B} (h : V₁ = V₂) {Y₁ Y₂ : Set B} (hY : Y₁ = Y₂) :
    (⟨V₁, subgroupOfX V₁ Y₁⟩ : Σ V : WeierstrassCurve B, AddSubgroup V.toAffine.Point) =
      ⟨V₂, subgroupOfX V₂ Y₂⟩ := by
  subst h hY; rfl

end P2MKcCQJbc
end P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed

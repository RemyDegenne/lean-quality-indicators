public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

theorem line_inter_pt : ∀ r s x : Pt, (x = 0 ∨ x = r ∨ x = r + r) →
    (x = 0 ∨ x = s ∨ x = s + s) → x ≠ 0 → (s = 0 ∨ s = r ∨ s = r + r) := by
  decide +kernel

end O3
end CFSG.Fischer.Classification
end

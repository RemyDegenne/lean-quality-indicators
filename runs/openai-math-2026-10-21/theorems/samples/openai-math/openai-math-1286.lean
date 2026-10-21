namespace OAI

open Set MeasureTheory

namespace BorsukNine.FiniteObstruction

attribute [local instance] Classical.propDecidable

variable {T Q : Family}

theorem c3072 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 5, 8} → ¬ T {4, 7, 9} → False := by
  intro a130 n78 n109
  have hc := h.complementary {0, 1, 3, 6} {2, 5, 8} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n78 (hc.mpr n109)

end BorsukNine.FiniteObstruction
end OAI

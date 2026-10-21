namespace OAI

open Set MeasureTheory

namespace BorsukNine.FiniteObstruction

attribute [local instance] Classical.propDecidable

variable {T Q : Family}

theorem c13703 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 6} → T {7, 8, 9} → False := by
  intro a206 a23 a120
  have hc := h.complementary {1, 2, 3, 5} {0, 4, 6} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 4, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a120

end BorsukNine.FiniteObstruction
end OAI

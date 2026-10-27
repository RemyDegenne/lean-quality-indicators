public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

open scoped Pointwise

section AMap

variable (hM : MatFacts) (α : MulAut J) (hE : ∀ x, α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11)

include hM hE

theorem amap_inj {c d : ℕ} (hc : c < 2 ^ 11) (hd : d < 2 ^ 11)
    (h : amap hM α hE c = amap hM α hE d) : c = d := by
  have h1 := amap_eta hM α hE hc
  have h2 := amap_eta hM α hE hd
  rw [h, ← h2] at h1
  exact eta_inj hM c hc d hd (α.injective h1)

end AMap
end CFSG.Sporadic.J4.QT
end

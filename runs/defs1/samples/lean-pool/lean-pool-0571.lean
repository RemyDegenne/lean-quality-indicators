@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

namespace Ingredients

variable {β : ℝ} (I : Ingredients β)

/-- The coefficient `ζ̂_{m,l_k}(s) ζ_{m,k}(s)` in `e.parabcorr.k`, `e.Chimk.formula`, `e.psi.m`. -/
def zetaProd (m : ℕ) (k : ℤ) (s : ℝ) : ℝ :=
  I.hatZetaML m (lIdx β I.Λ m k) s * I.zetaMK m k s

end Ingredients
end AVenhance
end
end
